module

public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsInclusion
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The inclusion of the sequence of principal parts, and its naturality

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site. The sequence of
principal parts (Tag 09CW) begins with a map `Ω_{O₂/O₁} ⊗ F ⟶ P¹_{O₂/O₁}(F)`, functorial in
the sheaf of `O₂`-modules `F`, whose symbol is `x ⊗ d b ↦ D (b x) - b D x` for the universal
differential operator `D` of order at most one out of `F`.

`StacksFrontier/CategoryTheory/Sites/Modules/PrincipalPartsInclusion.lean` constructs that map in
its *adjoint* form `Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹_{O₂/O₁}(F))`, for a fixed `F`, out of the
universal property of relative differentials (Tag 04BL). This file turns that into the
natural transformation the sequence asks for, in three steps: the evaluation pairing, which
converts a morphism into the internal hom into a morphism out of the objectwise tensor
product; naturality in `F`; and the sheafification adjunction, which replaces the objectwise
tensor product by the sheafified one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.evalTerminal`: evaluation of a section of the internal
  hom at the terminal object `id_U` of the slice site over `U`, as a linear map. This is the
  pairing of `𝓗om_O(M, P)(U)` with `M(U)`.
* `AlgebraicGeometry.SheafOfModules.pairingHom`: **the evaluation pairing** `M ⊗ N ⟶ P` of
  presheaves of modules attached to a family of sections of `𝓗om_O(M, P)` indexed by `N`.
  It is stated for a bare family of maps with three hypotheses, so that it applies to any
  morphism `N ⟶ 𝓗om_O(M, P)`; see the universe note below.
* `AlgebraicGeometry.SheafOfModules.internalHomComp`: pre-composition with `α : M ⟶ M'` and
  post-composition with `β : P ⟶ P'` on the internal hom, as a morphism of presheaves of
  modules `𝓗om_O(M', P) ⟶ 𝓗om_O(M, P')`.
* `AlgebraicGeometry.SheafOfModules.principalPartsPairingPresheaf`: the pairing
  `F ⊗ Ω_{O₂/O₁} ⟶ P¹_{O₂/O₁}(F)` of presheaves of modules, where the tensor product is the
  objectwise one.
* `AlgebraicGeometry.SheafOfModules.principalPartsInclusionApp`: its sheafified form, a
  morphism `(F ⊗ Ω_{O₂/O₁})^# ⟶ P¹_{O₂/O₁}(F)` of sheaves of modules.
* `AlgebraicGeometry.SheafOfModules.principalPartsInclusion`: **the inclusion of the sequence
  of principal parts**, as a natural transformation of endofunctors of sheaves of
  `O₂`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.evalTerminal_restr`: evaluation at the terminal object is
  compatible with restriction, which is what makes the pairing a morphism of presheaves.
* `AlgebraicGeometry.SheafOfModules.principalPartsInclusionHom_naturality`: the adjoint form
  of the inclusion is natural in `F`, in the sense that pre-composing with `f : F ⟶ G`
  the internal-hom form for `G` is post-composing with `P¹(f)` the one for `F`. This is the
  mathematical content of naturality, and it is proved by the uniqueness half of Tag 04BL:
  both sides are morphisms out of `Ω_{O₂/O₁}` carrying `d b` to the same commutator, because
  `f` is `O₂`-linear and `P¹(f)` intertwines the two universal operators.
* `AlgebraicGeometry.SheafOfModules.principalPartsPairingPresheaf_tmul_d` and
  `AlgebraicGeometry.SheafOfModules.principalPartsInclusionApp_toSheafify_tmul_d`: the
  pairing, before and after sheafification, carries `x ⊗ d b` to `D (b x) - b D x`. These
  pin the construction down; without them the natural transformation could be anything.

## Implementation notes

Universes, and a constraint. The site is `C : Type u` with `Category.{v} C` and the
structure sheaves are `CommRingCat.{w}`-valued. The internal hom `internalHom O M P` of
Tag 03EM lands in `PresheafOfModules.{max u v t}` when `M` and `P` lie in
`PresheafOfModules.{t}`, because its sections over `U` are morphisms on the slice site. A
morphism `N ⟶ internalHom O M P` therefore forces `N` into `PresheafOfModules.{max u v t}`,
and then the pairing `M ⊗ N ⟶ P` forces `t` to absorb `max u v`. Stating the pairing with
`M P N : PresheafOfModules.{max u v t}` and an argument `ι : N ⟶ internalHom O M P` does
*not* elaborate: Lean reports `stuck at solving universe constraint
max (max u v) ?u =?= max (max t u) v`, since `internalHom`'s own module universe appears
inside a `max` and the unifier will not solve for it. Explicit universe application does not
help. The cure used here is to take the evaluation data as a *bare family of maps*
`e : ∀ X, N.obj X → (M|_X ⟶ P|_X)` with additivity, linearity and restriction-compatibility
as explicit hypotheses. A function between types in different universes is unproblematic, so
`pairingHom` is stated with one free module universe `t` and no `max` at all; the universe
`max u v w m` of Tags 04BL and 09CT is then simply one instance of it, supplied with a
concrete term whose type is already determined. This is strictly more general than the
literal-universe form.

Spelling. `(Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj` and `O₂.obj ⋙ forget₂ CommRingCat
RingCat` are definitionally equal presheaves of rings, but `CategoryTheory.sheafCompose` unfolds at
neither reducible nor instance transparency, so neither `rw`/`simp` nor instance search can
cross between them, and no transparency option is set here. The devices are the ones of
`PrincipalPartsInclusion.lean`: every statement is ascribed at a single spelling and the
identities between spellings are discharged with `Eq.trans`, `congrArg` and `exact`, which
are checked up to definitional equality. Two consequences are worth recording. The
generic section uses `Oforget O` throughout, which is the spelling for which Mathlib's
`CommRing ((O ⋙ forget₂ _ _).obj X)` instance and `Module (R.obj X) (M.obj X)` fire; where a
section of the structure sheaf has to be read in the other spelling, the binder itself is
declared there (`b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X`) rather than ascribed
at the point of use, since a type ascription `(b : T)` leaves the variable's own type in place and
instance search then fails. And `restrFun_comp_add_comp` and `restrFun_comp_smulHom_comp` exist
only because `rw` with `Preadditive.add_comp` refuses a goal whose terms are elements of
`↑(internalHom O M P).obj X` rather than of the hom type it is definitionally equal to; stating
them on the plain hom type and applying them by `:=` crosses the gap.

What this file does *not* do. `internalHomComp`'s naturality, and the two whiskering
identities it rests on, hold by `rfl`: `homRestr`'s component at an object of the slice site
is the component of the original morphism at the relocalized object, and the `eqToHom`s in
the definition of `homRestr` sit at `rfl`-provable equalities of objects.

Nothing here is tagged. Tag 09CW's content is the short exact sequence
`0 → Ω_{O₂/O₁} ⊗ F → P¹(F) → F → 0`; this file supplies its first arrow and the arrow's
naturality, and the remaining obligation is exactness, which is the sectionwise statement
`LinearMap.IsDifferentialOperatorOfOrderLE.exists_shortExact_principalParts` (Tag 09CN)
together with `Stacks.Sheaves.PrincipalParts.principalPartsComparison`. The projection
`P¹(F) ⟶ F` and the functoriality of `P¹` are
`AlgebraicGeometry.SheafOfModules.principalPartsProjection` and
`AlgebraicGeometry.SheafOfModules.principalPartsFunctor`.

## References

* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal hom of
  sheaves of modules is a sheaf, and [Tag 04TT](https://stacks.math.columbia.edu/tag/04TT),
  the internal hom itself.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials, and [Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), principal parts.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

section Evaluation

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M P : PresheafOfModules.{t} (Oforget O))

/-- Restricting a section along the identity is the section itself. -/
theorem fRestr_terminal (U : C) (b : (Oforget O).obj (op U)) :
    fRestr O U b (op (Over.mk (𝟙 U))) = b := by
  change ((Oforget O).map (𝟙 (op U))).hom b = b
  rw [(Oforget O).map_id]
  rfl

/-- Evaluation at the terminal object of the slice site. -/
noncomputable def evalTerminal {X : Cᵒᵖ}
    (g : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) :
    M.obj X →ₗ[(Oforget O).obj X] P.obj X :=
  (g.app (op (Over.mk (𝟙 X.unop)))).hom

/-- `evalTerminal g` sends `a` to the component of `g` at the terminal object applied to `a`. -/
theorem evalTerminal_apply {X : Cᵒᵖ}
    (g : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) (a : M.obj X) :
    evalTerminal O M P g a = (g.app (op (Over.mk (𝟙 X.unop)))).hom a := rfl

/-- Evaluation at the terminal object is additive. -/
theorem evalTerminal_add {X : Cᵒᵖ}
    (g g' : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) :
    evalTerminal O M P (g + g') = evalTerminal O M P g + evalTerminal O M P g' := by
  apply LinearMap.ext
  intro a
  change ((g + g').app (op (Over.mk (𝟙 X.unop)))).hom a = _
  rw [PresheafOfModules.add_app]
  rfl

/-- Evaluation at the terminal object commutes with multiplication by a section. -/
theorem evalTerminal_smulHom {X : Cᵒᵖ} (r : (Oforget O).obj X)
    (g : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) :
    evalTerminal O M P (smulHom O M P X.unop r g) = r • evalTerminal O M P g := by
  apply LinearMap.ext
  intro a
  change ((g ≫ multEndoHom O P X.unop r).app (op (Over.mk (𝟙 X.unop)))).hom a = _
  rw [PresheafOfModules.comp_app]
  change fRestr O X.unop r (op (Over.mk (𝟙 X.unop))) •
    (g.app (op (Over.mk (𝟙 X.unop)))).hom a = _
  rw [fRestr_terminal]
  rfl

/-- Evaluation at the terminal object is compatible with restriction along `f`. -/
theorem evalTerminal_restr {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (g : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) (a : M.obj X) :
    evalTerminal O M P (homRestr O M P f.unop g) (M.map f a)
      = P.map f (evalTerminal O M P g a) := by
  have step1 : (toUnderlying O M P (homRestr O M P f.unop g)).app (op (Over.mk (𝟙 Y.unop)))
      = (toUnderlying O M P g).app (op (Over.mk f.unop)) := by
    rw [← toUnderlying_restr O M P f.unop g]
    exact presheafHom_map_app (F := M.presheaf) (G := P.presheaf)
      (𝟙 Y.unop) f.unop f.unop (Category.id_comp _) (toUnderlying O M P g)
  have hnat := PresheafOfModules.naturality_apply g
    ((Over.homMk f.unop (Category.comp_id _) :
      Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op) a
  refine Eq.trans ?_ hnat
  exact congrArg (fun k ↦ (ConcreteCategory.hom k) (M.map f a)) step1

end Evaluation

section Pairing

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M P N : PresheafOfModules.{t} (Oforget O))
  (e : ∀ X : Cᵒᵖ, N.obj X → ((restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P))
  (hadd : ∀ (X : Cᵒᵖ) (n n' : N.obj X), e X (n + n') = e X n + e X n')
  (hsmul : ∀ (X : Cᵒᵖ) (r : (Oforget O).obj X) (n : N.obj X),
    e X (r • n) = smulHom O M P X.unop r (e X n))

include hadd hsmul in
/-- The evaluation pairing at one object, as a bilinear map. -/
noncomputable def pairingBilin (X : Cᵒᵖ) :
    M.obj X →ₗ[(Oforget O).obj X] N.obj X →ₗ[(Oforget O).obj X] P.obj X :=
  LinearMap.flip
    { toFun n := evalTerminal O M P (e X n)
      map_add' n n' :=
        (congrArg (evalTerminal O M P) (hadd X n n')).trans
          (evalTerminal_add O M P _ _)
      map_smul' r n :=
        (congrArg (evalTerminal O M P) (hsmul X r n)).trans
          (evalTerminal_smulHom O M P r _) }

include hadd hsmul in
/-- The bilinear pairing sends `a` and `n` to the evaluation of `e X n` at `a`. -/
@[simp]
theorem pairingBilin_apply (X : Cᵒᵖ) (a : M.obj X) (n : N.obj X) :
    pairingBilin O M P N e hadd hsmul X a n = evalTerminal O M P (e X n) a := rfl

include hadd hsmul in
/-- The evaluation pairing at one object. -/
noncomputable def pairingApp (X : Cᵒᵖ) :
    (PresheafOfModules.tensorObj M N).obj X ⟶ P.obj X :=
  ModuleCat.ofHom (TensorProduct.lift (pairingBilin O M P N e hadd hsmul X))

include hadd hsmul in
/-- The pairing at one object sends `a ⊗ₜ n` to the evaluation of `e X n` at `a`. -/
@[simp]
theorem pairingApp_tmul (X : Cᵒᵖ) (a : M.obj X) (n : N.obj X) :
    (pairingApp O M P N e hadd hsmul X).hom (a ⊗ₜ[(Oforget O).obj X] n)
      = evalTerminal O M P (e X n) a := rfl

variable (hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (n : N.obj X),
  e Y (N.map f n) = homRestr O M P f.unop (e X n))

include hadd hsmul hnat in
/-- The pairings at the objects of the site are natural in the object. -/
theorem pairingApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (PresheafOfModules.tensorObj M N).map f ≫
        (ModuleCat.restrictScalars ((Oforget O).map f).hom).map
          (pairingApp O M P N e hadd hsmul Y) =
      pairingApp O M P N e hadd hsmul X ≫ P.map f := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a n
  refine Eq.trans (pairingApp_tmul O M P N e hadd hsmul Y (M.map f a) (N.map f n)) ?_
  rw [hnat f n]
  refine Eq.trans (evalTerminal_restr O M P f (e X n) a) ?_
  exact congrArg (fun z ↦ P.map f z) (pairingApp_tmul O M P N e hadd hsmul X a n).symm

include hadd hsmul hnat in
/-- The evaluation pairing. -/
noncomputable def pairingHom : PresheafOfModules.tensorObj M N ⟶ P where
  app X := pairingApp O M P N e hadd hsmul X
  naturality f := pairingApp_naturality O M P N e hadd hsmul hnat f

include hadd hsmul hnat in
/-- The evaluation pairing sends `a ⊗ₜ n` to the evaluation of `e X n` at `a`. -/
@[simp]
theorem pairingHom_app_tmul (X : Cᵒᵖ) (a : M.obj X) (n : N.obj X) :
    ((pairingHom O M P N e hadd hsmul hnat).app X).hom (a ⊗ₜ[(Oforget O).obj X] n)
      = evalTerminal O M P (e X n) a := rfl

end Pairing

section Composition

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M M' P P' : PresheafOfModules.{t} (Oforget O)) (α : M ⟶ M') (β : P ⟶ P')

/-- Restricting a morphism to the slice site commutes with multiplication by a section. -/
theorem multEndoHom_comp_restrFun_map (U : C) (r : (Oforget O).obj (op U)) :
    multEndoHom O P U r ≫ (restrFun O U).map β
      = (restrFun O U).map β ≫ multEndoHom O P' U r := by
  ext V x
  exact (β.app (op V.unop.left)).hom.map_smul (fRestr O U r V) x

/-- Additivity of pre- and post-composition, on the plain hom type. -/
theorem restrFun_comp_add_comp (X : Cᵒᵖ)
    (g g' : (restrFun O X.unop).obj M' ⟶ (restrFun O X.unop).obj P) :
    (restrFun O X.unop).map α ≫ (g + g') ≫ (restrFun O X.unop).map β =
      (restrFun O X.unop).map α ≫ g ≫ (restrFun O X.unop).map β +
        (restrFun O X.unop).map α ≫ g' ≫ (restrFun O X.unop).map β := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

/-- Linearity of pre- and post-composition, on the plain hom type. -/
theorem restrFun_comp_smulHom_comp (X : Cᵒᵖ) (r : (Oforget O).obj X)
    (g : (restrFun O X.unop).obj M' ⟶ (restrFun O X.unop).obj P) :
    (restrFun O X.unop).map α ≫ smulHom O M' P X.unop r g ≫
        (restrFun O X.unop).map β =
      smulHom O M P' X.unop r
        ((restrFun O X.unop).map α ≫ g ≫ (restrFun O X.unop).map β) := by
  rw [smulHom, smulHom, Category.assoc, Category.assoc, Category.assoc,
    multEndoHom_comp_restrFun_map]

/-- Pre-composition with `α` and post-composition with `β`, at one object of the site. -/
noncomputable def internalHomCompApp (X : Cᵒᵖ) :
    (internalHom O M' P).obj X ⟶ (internalHom O M P').obj X :=
  ModuleCat.homAddEquiv.symm
    { toFun g := (restrFun O X.unop).map α ≫ g ≫ (restrFun O X.unop).map β
      map_add' g g' := restrFun_comp_add_comp O M M' P P' α β X g g'
      map_smul' r g := restrFun_comp_smulHom_comp O M M' P P' α β X r g }

/-- `internalHomCompApp` sends `g` to `α ≫ g ≫ β`, restricted to the slice site. -/
@[simp]
theorem internalHomCompApp_apply (X : Cᵒᵖ) (g : (internalHom O M' P).obj X) :
    (internalHomCompApp O M M' P P' α β X).hom g
      = (restrFun O X.unop).map α ≫ g ≫ (restrFun O X.unop).map β := rfl

/-- **Pre-composition with `α` and post-composition with `β` on the internal hom.** -/
noncomputable def internalHomComp : internalHom O M' P ⟶ internalHom O M P' where
  app X := internalHomCompApp O M M' P P' α β X
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply PresheafOfModules.hom_ext
    intro W
    rfl

/-- The component of `internalHomComp` sends `g` to `α ≫ g ≫ β`, restricted to the slice site. -/
@[simp]
theorem internalHomComp_app_apply (X : Cᵒᵖ) (g : (internalHom O M' P).obj X) :
    ((internalHomComp O M M' P P' α β).app X).hom g
      = (restrFun O X.unop).map α ≫ g ≫ (restrFun O X.unop).map β := rfl

end Composition

section Inclusion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)
  (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- The presheaf-level evaluation pairing. -/
noncomputable def principalPartsPairingPresheaf :
    PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val ⟶
      (principalPartsOne.{v, u, w, m} φ F).val :=
  pairingHom O₂.obj F.val (principalPartsOne.{v, u, w, m} φ F).val
    (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val
    (fun X ω ↦ ((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom ω)
    (fun X ω ω' ↦ map_add ((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom ω ω')
    (fun X r ω ↦
      ((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom.map_smul r ω)
    (fun _ _ f ω ↦ PresheafOfModules.naturality_apply
      (principalPartsInclusionHom.{v, u, w, m} φ F).val f ω)

/-- The inclusion carries a differential `d b` to the commutator with `b` of the universal
operator of order at most one. -/
theorem principalPartsInclusionHom_d (X : Cᵒᵖ) (b : O₂.obj.obj X) :
    ((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom
        ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)
      = (principalPartsSymbolDerivation.{v, u, w, m} φ F).d b :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (postcomp_principalPartsInclusionHom.{v, u, w, m} φ F) b

/-- The presheaf-level pairing on a pure tensor. -/
theorem principalPartsPairingPresheaf_tmul (X : Cᵒᵖ) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    ((principalPartsPairingPresheaf.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] ω) =
      evalTerminal O₂.obj F.val (principalPartsOne.{v, u, w, m} φ F).val
        (((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom ω) x := rfl

/-- **The presheaf-level pairing is the symbol of the universal operator**: it carries
`x ⊗ d b` to `D (b x) - b D x`. -/
theorem principalPartsPairingPresheaf_tmul_d (X : Cᵒᵖ) (x : F.val.obj X)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) :
    ((principalPartsPairingPresheaf.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X]
          (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X
          (b • x) -
        b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x := by
  refine Eq.trans (principalPartsPairingPresheaf_tmul.{v, u, w, m} φ F X x _) ?_
  refine Eq.trans (congrArg
    (fun g : (restrFun O₂.obj X.unop).obj F.val ⟶
        (restrFun O₂.obj X.unop).obj (principalPartsOne.{v, u, w, m} φ F).val ↦
      evalTerminal O₂.obj F.val (principalPartsOne.{v, u, w, m} φ F).val (X := X) g x)
    (principalPartsInclusionHom_d.{v, u, w, m} φ F X b)) ?_
  exact congrArg
    (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X ↦
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (r • x) -
        r • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x)
    (fRestr_terminal O₂.obj X.unop b)

variable (G : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- Pre-composition with `f : F ⟶ G` on the internal hom into `P¹(G)`. -/
noncomputable def principalPartsPrecomp (f : F ⟶ G) :
    internalHomSheafOfModules G (principalPartsOne.{v, u, w, m} φ G) ⟶
      internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ G) :=
  ⟨internalHomComp O₂.obj F.val G.val (principalPartsOne.{v, u, w, m} φ G).val
    (principalPartsOne.{v, u, w, m} φ G).val f.val (𝟙 _)⟩

/-- Post-composition with `P¹(f)` on the internal hom out of `F`. -/
noncomputable def principalPartsPostcomp (f : F ⟶ G) :
    internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F) ⟶
      internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ G) :=
  ⟨internalHomComp O₂.obj F.val F.val (principalPartsOne.{v, u, w, m} φ F).val
    (principalPartsOne.{v, u, w, m} φ G).val (𝟙 _)
    (principalPartsMap.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1).val⟩

/-- **The inclusion is natural in the coefficient module**, in internal-hom form. -/
theorem principalPartsInclusionHom_naturality (f : F ⟶ G) :
    principalPartsInclusionHom.{v, u, w, m} φ G ≫ principalPartsPrecomp φ F G f =
      principalPartsInclusionHom.{v, u, w, m} φ F ≫ principalPartsPostcomp φ F G f := by
  refine (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
      (principalPartsInclusionHom.{v, u, w, m} φ F ≫
        principalPartsPostcomp φ F G f).val)).unique ?_ rfl
  ext X b
  refine Eq.trans (congrArg
    (fun z ↦ ((principalPartsPrecomp φ F G f).val.app X).hom z)
    (principalPartsInclusionHom_d.{v, u, w, m} φ G X b)) ?_
  refine Eq.trans ?_ (congrArg
    (fun z ↦ ((principalPartsPostcomp φ F G f).val.app X).hom z)
    (principalPartsInclusionHom_d.{v, u, w, m} φ F X b)).symm
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact diffOpSymbol_restriction (RingHom.id _)
    (f.val.app (op V.unop.left)).hom.toAddMonoidHom
    ((principalPartsMap.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1).val.app
      (op V.unop.left)).hom.toAddMonoidHom
    (fun r y ↦ (f.val.app (op V.unop.left)).hom.map_smul r y)
    (fun r y ↦ ((principalPartsMap.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) f 1).val.app (op V.unop.left)).hom.map_smul r y)
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 (op V.unop.left))
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) G 1 (op V.unop.left))
    (fun y ↦ (principalPartsMap_universalDiffOp.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) f 1 (op V.unop.left) y).symm)
    (fRestr O₂.obj X.unop b V) x

/-- **The presheaf-level pairing is natural in the coefficient module.** -/
theorem principalPartsPairingPresheaf_naturality (f : F ⟶ G) :
    (PresheafOfModules.tensorRight
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).map f.val ≫
        principalPartsPairingPresheaf.{v, u, w, m} φ G =
      principalPartsPairingPresheaf.{v, u, w, m} φ F ≫
        (principalPartsMap.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1).val := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a ω
  exact congrArg
    (fun k : (restrFun O₂.obj X.unop).obj F.val ⟶
        (restrFun O₂.obj X.unop).obj (principalPartsOne.{v, u, w, m} φ G).val ↦
      (k.app (op (Over.mk (𝟙 X.unop)))).hom a)
    (congrArg
      (fun k : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
          internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ G) ↦
        (ConcreteCategory.hom (k.val.app X)) ω)
      (principalPartsInclusionHom_naturality φ F G f))

end Inclusion

section Transformation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)

variable (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- The inclusion of the sequence of principal parts, at one coefficient module. -/
noncomputable def principalPartsInclusionApp :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ)).obj F ⟶
      (principalPartsFunctor.{v, u, w, m} (underlyingRingSheafMapOfSite φ) 1).obj F :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).symm
    (principalPartsPairingPresheaf.{v, u, w, m} φ F)

/-- **The inclusion at one module is the symbol of the universal operator**: on the image of
the pure tensor `x ⊗ d b` under the sheafification map it is `D (b x) - b D x`. -/
theorem principalPartsInclusionApp_toSheafify_tmul_d (X : Cᵒᵖ) (x : F.val.obj X)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) :
    ((principalPartsInclusionApp.{v, u, w, m} φ F).val.app X).hom
        (((toSheafify J (PresheafOfModules.tensorObj F.val
            (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).presheaf).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X
          (b • x) -
        b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
    (principalPartsInclusionApp.{v, u, w, m} φ F)
  rw [show PresheafOfModules.sheafificationHomEquiv
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
        (principalPartsInclusionApp.{v, u, w, m} φ F) =
      principalPartsPairingPresheaf.{v, u, w, m} φ F from
    Equiv.apply_symm_apply ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv
      (PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val)
      (principalPartsOne.{v, u, w, m} φ F))
      (principalPartsPairingPresheaf.{v, u, w, m} φ F)] at h
  refine Eq.trans ?_ (principalPartsPairingPresheaf_tmul_d.{v, u, w, m} φ F X x b)
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h X) _).symm

/-- **The inclusion of the sequence of principal parts.** -/
noncomputable def principalPartsInclusion :
    (Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ) ⟶
      principalPartsFunctor.{v, u, w, m} (underlyingRingSheafMapOfSite φ) 1 where
  app A := principalPartsInclusionApp.{v, u, w, m} φ A
  naturality {A B} f :=
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv_naturality_left_symm
      ((PresheafOfModules.tensorRight
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).map f.val)
      (principalPartsPairingPresheaf.{v, u, w, m} φ B)).symm.trans
    ((congrArg ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).symm
      (principalPartsPairingPresheaf_naturality.{v, u, w, m} φ A B f)).trans
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv_naturality_right_symm
      (principalPartsPairingPresheaf.{v, u, w, m} φ A)
      (principalPartsMap.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1)))

/-- The component of `principalPartsInclusion` at `F` is `principalPartsInclusionApp φ F`. -/
@[simp]
theorem principalPartsInclusion_app : (principalPartsInclusion.{v, u, w, m} φ).app F =
    principalPartsInclusionApp.{v, u, w, m} φ F := rfl

/-- **The inclusion of the sequence of principal parts is the symbol of the universal
operator of order at most one**: on the image of the pure tensor `x ⊗ d b` under the
sheafification map it is `D (b x) - b D x`. This pins the natural transformation down. -/
theorem principalPartsInclusion_toSheafify_tmul_d (X : Cᵒᵖ) (x : F.val.obj X)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) :
    (((principalPartsInclusion.{v, u, w, m} φ).app F).val.app X).hom
        (((toSheafify J (PresheafOfModules.tensorObj F.val
            (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).presheaf).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x) -
        b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x :=
  principalPartsInclusionApp_toSheafify_tmul_d.{v, u, w, m} φ F X x b

end Transformation

end AlgebraicGeometry.SheafOfModules
