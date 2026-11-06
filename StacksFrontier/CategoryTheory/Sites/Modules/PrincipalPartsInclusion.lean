module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsCorepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The inclusion of the sequence of principal parts, through the internal hom

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site and let `F` be a
sheaf of `O₂`-modules. The sequence of principal parts (Tag 09CW) begins with a map
`Ω_{O₂/O₁} ⊗ F ⟶ P¹_{O₂/O₁}(F)`, the symbol `x ⊗ d b ↦ D (b x) - b D x` of the universal
differential operator `D` of order at most one out of `F`.

This file constructs that map in its *adjoint* form,
`Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹_{O₂/O₁}(F))`,
by the universal property of the sheaf of relative differentials (Tag 04BL). The step that
makes this possible is Tag 03EM: the internal hom of a presheaf of modules into a *sheaf* of
modules is a sheaf of modules, so the corepresentability of relative derivations applies to
it. The commutator `b ↦ (x ↦ D (b x) - b D x)` is exactly a relative derivation with values
in that internal hom, and the Leibniz rule for it is the one place the order-at-most-one
condition is used.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.bracketCore`: the commutator of an additive operator
  `D : M → P` of presheaves of modules with a section of the structure presheaf, at one
  object, as a morphism of modules. Its linearity *is* order at most one.
* `AlgebraicGeometry.SheafOfModules.internalHomBracketApp` and
  `AlgebraicGeometry.SheafOfModules.internalHomBracket`: the commutator with a section
  `b ∈ O₂(U)`, at an object of the slice site over `U` and then as a whole morphism
  `M|_U ⟶ P|_U`, i.e. a section over `U` of the internal hom of Tag 03EM.
* `AlgebraicGeometry.SheafOfModules.internalHomDerivation`: the commutator, as a relative
  derivation with values in `𝓗om_{O₂}(M, P)`.
* `AlgebraicGeometry.SheafOfModules.internalHomSheafOfModules`: the internal hom of two
  sheaves of modules, as a sheaf of modules (Tag 03EM).
* `AlgebraicGeometry.SheafOfModules.principalPartsSymbolDerivation`: that derivation for the
  universal operator of order at most one out of `F`.
* `AlgebraicGeometry.SheafOfModules.principalPartsInclusionHom`: the resulting morphism
  `Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹_{O₂/O₁}(F))`.

## Main results

* `AlgebraicGeometry.SheafOfModules.bracketCore_mul_apply`: the Leibniz rule
  `[b b', -] = b [b', -] + b' [b, -]`, the only use of order at most one.
* `AlgebraicGeometry.SheafOfModules.internalHomBracketApp_naturality` and
  `AlgebraicGeometry.SheafOfModules.internalHomBracket_restr`: the commutator is compatible
  with restriction along the slice site and with restriction of the section, which is what
  makes it a morphism of presheaves of modules and then a derivation.
* `AlgebraicGeometry.SheafOfModules.postcomp_principalPartsInclusionHom` and
  `AlgebraicGeometry.SheafOfModules.principalPartsInclusionHom_unique`: the inclusion is the
  unique morphism out of `Ω_{O₂/O₁}` whose composite with the universal derivation is the
  symbol derivation.

## Implementation notes

The construction is stated twice. The commutator and its derivation property are proved for
*presheaves* of modules over `Oforget O₂ = O₂ ⋙ forget₂ CommRingCat RingCat` and for a bare
family of additive maps `D` together with three hypotheses — `hbr` (order at most one),
`hnat` (compatibility with restriction) and `hbase` (linearity over the base). Nothing about
bundled differential operators is used, so the same construction applies to any
order-at-most-one operator. Only then is it instantiated at the universal operator of
Tag 09CT, which is where the sheaf-theoretic spellings enter.

Spelling discipline. `Stacks.SheafOfModules.Tensor.ringSheaf O₂` and `Oforget O₂.obj` are
definitionally equal presheaves of rings, but `CategoryTheory.sheafCompose` sits between them and
unfolds at neither reducible nor instance transparency, so `rw` and `simp` cannot cross and
instance search does not see through. Two devices are used, and no transparency option is set.
First, `bracketCore` is the single canonical spelling of the commutator, over `Oforget O₂`, where
Mathlib's instance `Module (R.obj X) (M.obj X)` for a presheaf of modules over `R ⋙ forget₂ _ _`
fires; every slice-site form is *defined* from it by ascription (`internalHomBracketApp`) and never
rewritten into it. Second, the identities relating two spellings are discharged with `Eq.trans` and
`congrArg` applied by `exact`, which are checked up to definitional equality, rather than with
`rw`; `internalHomBracket_restr` is the clearest case, where the two sides differ only in which
slice object the restricted section is read at. The two spellings meet exactly once, when
`principalPartsSymbolDerivation` feeds `F.val` and the lemmas about the universal operator into
the presheaf-level construction.

Universes. The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued, and the presheaf-level section is polymorphic in a free module
universe `t`. Note that `internalHomSheafOfModules` lands in `SheafOfModules.{max u v t}`
rather than `SheafOfModules.{t}`: its sections over `U` are the morphisms `F|_U ⟶ G|_U` on
the slice site, and hom types of presheaves of modules on this site live in
`Type (max u v t)`. This is forced, not chosen. The universe `max u v w m` of Tags 04BL and
09CT is closed under it, which is exactly why the construction closes up; it would not close
up at a module universe not absorbing `max u v`.

This file also depends on Tag 03EM being available at an *independent* module universe. The
statement `internalHom_isSheaf` is universe-polymorphic in the module universe, so it applies
at `max u v w m`; nothing here narrows it.

## What is not here

Tag 09CW asks for a short exact sequence `0 → Ω_{O₂/O₁} ⊗ F → P¹(F) → F → 0` of sheaves of
modules, functorial in `F`. What this file provides is the adjoint form of its first map, for
a fixed `F`. Three things remain. The evaluation pairing turning
`Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹(F))` into a morphism `F ⊗ Ω_{O₂/O₁} ⟶ P¹(F)` of presheaves of
modules, and then, through the sheafification adjunction
`PresheafOfModules.sheafificationAdjunction`, into a morphism out of the sheafified tensor
product. Naturality in `F`, which must be checked against
`AlgebraicGeometry.SheafOfModules.principalPartsFunctor`. And exactness, which is the
sectionwise statement
`LinearMap.IsDifferentialOperatorOfOrderLE.exists_shortExact_principalParts` (Tag 09CN)
together with `Stacks.Sheaves.PrincipalParts.principalPartsComparison`.

## References

* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal hom of
  sheaves of modules is a sheaf.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials, and [Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), principal parts.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

section InternalHomBracket

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : O₁ ⟶ O₂)
  (M P : PresheafOfModules.{t} (Oforget O₂)) (D : ∀ X : Cᵒᵖ, M.obj X →+ P.obj X)
  (hbr : ∀ (X : Cᵒᵖ) (b r : O₂.obj X) (x : M.obj X),
    D X (b • r • x) - b • D X (r • x) = r • (D X (b • x) - b • D X x))

/-- The commutator of `D` with a section `s ∈ O(X)` over the *same* object `X`, as a
morphism `M(X) ⟶ P(X)` of `O(X)`-modules: the map `x ↦ D (s x) - s D x`. Its linearity is
exactly the order-at-most-one condition `hbr`.

This is the canonical spelling of the commutator, over `Oforget O₂`; the slice-site
spellings below are all defined from it, never rewritten into it. -/
noncomputable def bracketCore (X : Cᵒᵖ) (s : (Oforget O₂).obj X) : M.obj X ⟶ P.obj X :=
  ModuleCat.homAddEquiv.symm
    { toFun x := D X (s • x) - s • D X x
      map_add' x y := by
        simp only [smul_add, map_add]
        abel
      map_smul' r x := hbr X s r x }

/-- The commutator `bracketCore` sends `x` to `D (s • x) - s • D x`. -/
@[simp]
theorem bracketCore_apply (X : Cᵒᵖ) (s : (Oforget O₂).obj X) (x : M.obj X) :
    (bracketCore M P D hbr X s).hom x = D X (s • x) - s • D X x := rfl

/-- The commutator is additive in the section, on elements: `[s + s', x] = [s, x] + [s', x]`. -/
theorem bracketCore_add_apply (X : Cᵒᵖ) (s s' : (Oforget O₂).obj X) (x : M.obj X) :
    (bracketCore M P D hbr X (s + s')).hom x =
      (bracketCore M P D hbr X s).hom x + (bracketCore M P D hbr X s').hom x := by
  simp only [bracketCore_apply, add_smul, map_add]
  abel

/-- **The Leibniz rule for the commutator**, on elements. This is the one place the
order-at-most-one condition `hbr` is used. -/
theorem bracketCore_mul_apply (X : Cᵒᵖ) (s s' : (Oforget O₂).obj X) (x : M.obj X) :
    (bracketCore M P D hbr X (s * s')).hom x =
      s • (bracketCore M P D hbr X s').hom x + s' • (bracketCore M P D hbr X s).hom x := by
  simp only [bracketCore_apply, mul_smul, smul_sub]
  rw [sub_eq_iff_eq_add.1 (hbr X s s' x), smul_sub]
  abel

/-- The commutator is additive in the section: `[s + s', -] = [s, -] + [s', -]`. -/
theorem bracketCore_add (X : Cᵒᵖ) (s s' : (Oforget O₂).obj X) :
    bracketCore M P D hbr X (s + s') =
      bracketCore M P D hbr X s + bracketCore M P D hbr X s' := by
  ext x
  simpa only [ModuleCat.hom_add, LinearMap.add_apply] using
    bracketCore_add_apply M P D hbr X s s' x

/-- The commutator with a section coming from the base vanishes: that is the linearity of
`D` over the base presheaf of rings. -/
theorem bracketCore_base
    (hbase : ∀ (X : Cᵒᵖ) (a : O₁.obj X) (x : M.obj X),
      D X ((φ.app X).hom a • x) = (φ.app X).hom a • D X x)
    (X : Cᵒᵖ) (a : O₁.obj X) :
    bracketCore M P D hbr X ((φ.app X).hom a) = 0 := by
  ext x
  simp only [bracketCore_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [hbase X a x, sub_self]

/-- The commutator of `D` with (the restriction of) a section `b ∈ O(U)`, at an object `V`
of the slice site over `U`. It is `bracketCore` at `V.left`, read in the slice spelling. -/
noncomputable def internalHomBracketApp (U : C) (b : (Oforget O₂).obj (op U))
    (V : (Over U)ᵒᵖ) :
    ((restrFun O₂ U).obj M).obj V ⟶ ((restrFun O₂ U).obj P).obj V :=
  bracketCore M P D hbr (op V.unop.left) (fRestr O₂ U b V)

variable (hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : M.obj X), D Y (M.map f x) = P.map f (D X x))

include hnat in
/-- The commutator with a section is compatible with restriction along the slice site,
hence assembles into a morphism of presheaves of modules on the slice site. -/
theorem internalHomBracketApp_naturality (U : C) (b : (Oforget O₂).obj (op U))
    ⦃V W : (Over U)ᵒᵖ⦄ (g : V ⟶ W) :
    ((restrFun O₂ U).obj M).map g ≫
        (ModuleCat.restrictScalars ((ORestr O₂ U).map g).hom).map
          (internalHomBracketApp M P D hbr U b W) =
      internalHomBracketApp M P D hbr U b V ≫ ((restrFun O₂ U).obj P).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, internalHomBracketApp]
  have hscalar : fRestr O₂ U b W = ((ORestr O₂ U).map g).hom (fRestr O₂ U b V) := by
    show ((Oforget O₂).map W.unop.hom.op).hom b
        = ((Oforget O₂).map ((Over.forget U).map g.unop).op).hom
            (((Oforget O₂).map V.unop.hom.op).hom b)
    have hcomp : ((Over.forget U).map g.unop) ≫ V.unop.hom = W.unop.hom := Over.w g.unop
    rw [← hcomp, op_comp, Functor.map_comp]
    rfl
  rw [hscalar]
  exact diffOpSymbol_restriction ((ORestr O₂ U).map g).hom
    (((restrFun O₂ U).obj M).map g).hom.toAddMonoidHom
    (((restrFun O₂ U).obj P).map g).hom.toAddMonoidHom
    (fun r y => (((restrFun O₂ U).obj M).map g).hom.map_smul r y)
    (fun r y => (((restrFun O₂ U).obj P).map g).hom.map_smul r y)
    (D (op V.unop.left)) (D (op W.unop.left))
    (fun y => hnat ((Over.forget U).map g.unop).op y) (fRestr O₂ U b V) x

include hnat in
/-- The commutator of `D` with a section `b ∈ O(U)`, as a morphism `M|_U ⟶ P|_U` of
presheaves of modules on the slice site over `U`: a section over `U` of the internal hom
`𝓗om_{O₂}(M, P)` of Tag 03EM. -/
noncomputable def internalHomBracket (U : C) (b : (Oforget O₂).obj (op U)) :
    (restrFun O₂ U).obj M ⟶ (restrFun O₂ U).obj P where
  app V := internalHomBracketApp M P D hbr U b V
  naturality g := internalHomBracketApp_naturality M P D hbr hnat U b g

include hnat in
/-- The component of `internalHomBracket` at an object `V` of the slice site over `U` is the
commutator `bracketCore` at `V.left` with the restriction of `b` to `V`. -/
@[simp]
theorem internalHomBracket_app (U : C) (b : (Oforget O₂).obj (op U)) (V : (Over U)ᵒᵖ) :
    (internalHomBracket M P D hbr hnat U b).app V =
      bracketCore M P D hbr (op V.unop.left) (fRestr O₂ U b V) := rfl

/-- Additivity of restriction of sections. -/
private theorem fRestr_add (U : C) (b b' : (Oforget O₂).obj (op U)) (V : (Over U)ᵒᵖ) :
    fRestr O₂ U (b + b') V = fRestr O₂ U b V + fRestr O₂ U b' V := by
  rw [fRestr, fRestr, fRestr, map_add]
  rfl

include hnat in
/-- The morphism `internalHomBracket` is additive in the section `b`. -/
theorem internalHomBracket_add (U : C) (b b' : (Oforget O₂).obj (op U)) :
    internalHomBracket M P D hbr hnat U (b + b') =
      internalHomBracket M P D hbr hnat U b + internalHomBracket M P D hbr hnat U b' := by
  apply PresheafOfModules.hom_ext
  intro V
  rw [PresheafOfModules.add_app, internalHomBracket_app, internalHomBracket_app,
    internalHomBracket_app, fRestr_add]
  exact bracketCore_add M P D hbr (op V.unop.left) _ _

include hnat in
/-- The commutator is compatible with restriction of the section: restricting the morphism
`M|_U ⟶ P|_U` along `f` is the commutator with the restricted section. -/
theorem internalHomBracket_restr {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : (Oforget O₂).obj X) :
    homRestr O₂ M P f.unop (internalHomBracket M P D hbr hnat X.unop b) =
      internalHomBracket M P D hbr hnat Y.unop (((Oforget O₂).map f).hom b) := by
  apply PresheafOfModules.hom_ext
  intro W
  have hscalar : fRestr O₂ Y.unop (((Oforget O₂).map f).hom b) W
      = fRestr O₂ X.unop b ((Over.map f.unop).op.obj W) := by
    show ((Oforget O₂).map W.unop.hom.op).hom (((Oforget O₂).map f).hom b)
        = ((Oforget O₂).map ((Over.map f.unop).obj W.unop).hom.op).hom b
    have hcomp : ((Over.map f.unop).obj W.unop).hom = W.unop.hom ≫ f.unop := rfl
    rw [hcomp, op_comp, Functor.map_comp]
    rfl
  exact (congrArg (bracketCore M P D hbr (op W.unop.left)) hscalar).symm

/-- Multiplicativity of restriction of sections, in the form the Leibniz rule needs. -/
theorem fRestr_mul (U : C) (b b' : (Oforget O₂).obj (op U)) (V : (Over U)ᵒᵖ) :
    fRestr O₂ U (b * b') V = fRestr O₂ U b V * fRestr O₂ U b' V := by
  rw [fRestr, fRestr, fRestr, map_mul]
  rfl

variable (hbase : ∀ (X : Cᵒᵖ) (a : O₁.obj X) (x : M.obj X),
    D X ((φ.app X).hom a • x) = (φ.app X).hom a • D X x)

include hnat hbase in
/-- The commutator with a section coming from the base vanishes. -/
theorem internalHomBracket_base (U : C) (a : O₁.obj (op U)) :
    internalHomBracket M P D hbr hnat U ((φ.app (op U)).hom a) = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  rw [PresheafOfModules.zero_app, internalHomBracket_app]
  have hb : fRestr O₂ U ((φ.app (op U)).hom a) V
      = (φ.app (op V.unop.left)).hom ((O₁.map V.unop.hom.op).hom a) := by
    show ((Oforget O₂).map V.unop.hom.op).hom ((φ.app (op U)).hom a) = _
    exact congrFun (congrArg (fun g : O₁.obj (op U) ⟶ O₂.obj (op V.unop.left) =>
      (ConcreteCategory.hom g : O₁.obj (op U) → O₂.obj (op V.unop.left)))
      (φ.naturality V.unop.hom.op).symm) a
  exact (congrArg (bracketCore M P D hbr (op V.unop.left)) hb).trans
    (bracketCore_base φ M P D hbr hbase (op V.unop.left) _)

include hnat hbase in
/-- **The commutator of `D` with the sections of `O₂`, as a relative derivation with values
in the internal hom `𝓗om_{O₂}(M, P)`.** This is the universal-property form of the symbol
of `D`: the sheaf of relative differentials can be mapped out of it by Tag 04BL, which is
what replaces a comparison with the presheaf of objectwise Kähler differentials. -/
noncomputable def internalHomDerivation :
    PresheafOfModulesOfCommRing.Derivation' (internalHom O₂ M P) φ where
  d {X} := AddMonoidHom.mk' (fun b => internalHomBracket M P D hbr hnat X.unop b)
    (internalHomBracket_add M P D hbr hnat X.unop)
  d_mul {X} a b := by
    refine PresheafOfModules.hom_ext fun V => ?_
    ext x
    exact (congrArg (fun s => (bracketCore M P D hbr (op V.unop.left) s).hom x)
        (fRestr_mul (O₂ := O₂) X.unop a b V)).trans
      (bracketCore_mul_apply M P D hbr (op V.unop.left) _ _ x)
  d_map {X Y} f x := (internalHomBracket_restr M P D hbr hnat f x).symm
  d_app {X} a := internalHomBracket_base φ M P D hbr hnat hbase X.unop a

include hnat hbase in
/-- The derivation `internalHomDerivation` sends a section `b ∈ O₂(X)` to the commutator
`internalHomBracket` with `b`. -/
@[simp]
theorem internalHomDerivation_d (X : Cᵒᵖ) (b : O₂.obj X) :
    (internalHomDerivation φ M P D hbr hnat hbase).d b =
      internalHomBracket M P D hbr hnat X.unop b := rfl

end InternalHomBracket

section Inclusion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)

/-- **The internal hom of two sheaves of modules is a sheaf of modules.** This is Tag 03EM
packaged as an object of `SheafOfModules`: the underlying presheaf is `internalHom` and the
sheaf condition is `internalHom_isSheaf`, which needs only the target to be a sheaf.

The module universe of the result is `max u v t`, not `t`: the sections over `U` are the
morphisms `F|_U ⟶ G|_U` on the slice site, and hom types of presheaves of modules on a site
with objects in `Type u` and morphisms in `Type v` live in `Type (max u v t)`. The universe
`max u v w m` of Tags 04BL and 09CT is closed under this, which is what makes the
construction below possible. -/
@[sga "4 IV 12.1" "partial"]
noncomputable def internalHomSheafOfModules
    (F G : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    _root_.SheafOfModules.{max u v t} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) where
  val := internalHom O₂.obj F.val G.val
  isSheaf := internalHom_isSheaf O₂.obj F.val G.val G.isSheaf

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying presheaf of modules of `internalHomSheafOfModules F G` is the internal hom
`internalHom` of the underlying presheaves. -/
theorem internalHomSheafOfModules_val
    (F G : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (internalHomSheafOfModules F G).val = internalHom O₂.obj F.val G.val := rfl

variable (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- The sheaf of principal parts of order at most one, as the target of the commutator. -/
noncomputable abbrev principalPartsOne :
    _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1

/-- **The symbol of the universal order-one operator, as a relative derivation with values
in `𝓗om_{O₂}(F, P¹(F))`.** By Tag 03EM that internal hom is a sheaf of modules, so Tag 04BL
applies to it; this is what lets the sheaf of relative differentials be mapped out of it
without comparing it to the presheaf of objectwise Kähler differentials. -/
@[ega "IV 16.11.1" "special case"]
noncomputable def principalPartsSymbolDerivation :
    PresheafOfModulesOfCommRing.Derivation'
      (internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F)).val φ.hom :=
  internalHomDerivation φ.hom F.val (principalPartsOne.{v, u, w, m} φ F).val
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1)
    (fun X b r x => isGlobalDiffOpOfOrder_one_bracket _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) X b r x)
    (fun {_ _} f x => globalDiffOp_naturality _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) f x)
    (fun X a x => isGlobalDiffOpOfOrder_one_base _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) X a x)

/-- **The inclusion of the sequence of principal parts, in internal-hom form.** The morphism
`Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹_{O₂/O₁}(F))` obtained from the universal property of the sheaf
of relative differentials (Tag 04BL) applied to the symbol derivation: it sends a
differential `d b` to the commutator `x ↦ D (b x) - b D x` of the universal operator of
order at most one. -/
noncomputable def principalPartsInclusionHom :
    moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
      internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F) :=
  (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    (principalPartsSymbolDerivation φ F)).choose

/-- **The inclusion is pinned by the symbol formula.** Composing the universal derivation
with `principalPartsInclusionHom` recovers the symbol derivation, i.e. the differential
`d b` is carried to the commutator of the universal operator with `b`. -/
theorem postcomp_principalPartsInclusionHom :
    (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
        (principalPartsInclusionHom.{v, u, w, m} φ F).val =
      principalPartsSymbolDerivation φ F :=
  (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    (principalPartsSymbolDerivation φ F)).choose_spec.1

/-- The inclusion is the unique morphism out of `Ω_{O₂/O₁}` with that property. -/
theorem principalPartsInclusionHom_unique
    (g : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
      internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F))
    (hg : (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp g.val =
      principalPartsSymbolDerivation φ F) :
    g = principalPartsInclusionHom.{v, u, w, m} φ F :=
  (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    (principalPartsSymbolDerivation φ F)).choose_spec.2 g hg

end Inclusion

end AlgebraicGeometry.SheafOfModules
