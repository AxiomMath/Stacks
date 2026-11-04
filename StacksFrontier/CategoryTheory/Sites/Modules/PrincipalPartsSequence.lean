module

public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# The sequence of principal parts: the complex, its exactness and its surjection

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site and let `F` be a
sheaf of `O₂`-modules. Tag 09CW asserts that the two canonical maps of the sequence of
principal parts
`0 → Ω_{O₂/O₁} ⊗_{O₂} F → P¹_{O₂/O₁}(F) → F → 0`
form a short exact sequence, functorially in `F`. The two maps and their naturality are
`AlgebraicGeometry.SheafOfModules.principalPartsInclusion` and
`AlgebraicGeometry.SheafOfModules.principalPartsProjection`. This file proves that they
form a *complex*, that the projection is an *epimorphism*, and that the complex is *exact*
in the middle; the remaining clause, that the inclusion is a monomorphism, is not proved
here (see the implementation notes).

## Main definitions

* `AlgebraicGeometry.SheafOfModules.principalPartsPostcompRetraction`: post-composition with
  the projection `P¹_{O₂/O₁}(F) ⟶ F`, as a morphism of internal homs.
* `AlgebraicGeometry.SheafOfModules.descPrincipalParts`: the factorization through the
  projection of a morphism out of `P¹_{O₂/O₁}(F)` that annihilates the inclusion. On local
  sections it is `x ↦ k (D x)` for the universal operator `D` of order at most one.
* `AlgebraicGeometry.SheafOfModules.isColimitCokernelCoforkPrincipalParts`: the projection
  is a cokernel of the inclusion.

## Main results

* `AlgebraicGeometry.SheafOfModules.principalPartsInclusion_comp_projection`: **the sequence
  of principal parts is a complex.** The composite of the two maps vanishes.
* `AlgebraicGeometry.SheafOfModules.epi_principalPartsProjection_app`: **the projection is an
  epimorphism.**
* `AlgebraicGeometry.SheafOfModules.shortComplex_exact_principalParts`: **the sequence of
  principal parts is exact in the middle.**
* `AlgebraicGeometry.SheafOfModules.exists_shortExact_principalPartsSequence`: Tag 09CW's
  short-exactness clause, under the one hypothesis this file does not discharge, namely that
  the inclusion is a monomorphism.
* `AlgebraicGeometry.SheafOfModules.tensorHom_eq_zero`: a morphism out of an objectwise
  tensor product of presheaves of modules vanishes as soon as it vanishes on pure tensors.
* `AlgebraicGeometry.SheafOfModules.eq_zero_of_adjunction_homEquiv_eq_zero`: a morphism out
  of the image of a left adjoint vanishes as soon as its adjoint transpose does.

## Implementation notes

*The complex.* That the composite vanishes is not a computation on sections of
`(Ω_{O₂/O₁} ⊗ F)^#`, whose elements are not of the form `x ⊗ d b`: it is the uniqueness half
of Tag 04BL. The inclusion is, in adjoint form, a morphism
`ι : Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, P¹_{O₂/O₁}(F))`, and post-composing it with the projection
gives a morphism out of `Ω_{O₂/O₁}` whose composite with the universal derivation carries
`d b` to `x ↦ b x - b x = 0`. Since a morphism out of `Ω_{O₂/O₁}` is determined by that
composite, the post-composed morphism is zero, and then the pairing is zero on every pure
tensor `x ⊗ ω` — for *arbitrary* `ω`, not only for `ω = d b`. The sheafification adjunction
transports that to the sheaf level. This is why no statement about local generation of
`Ω_{O₂/O₁}` by the differentials is needed anywhere below.

*Exactness and the surjection.* These are both free once the complex is available, and
neither needs the commutative-algebra sequence of Tag 09CN. The projection is surjective on
local sections, because the universal operator is a set-theoretic section of it, hence
locally surjective, hence epi. And the projection is a *cokernel* of the inclusion: if
`k : P¹_{O₂/O₁}(F) ⟶ T` annihilates the inclusion then `x ↦ k (D x)` is `O₂`-linear,
precisely because the failure of `D` to be linear is `D (b x) - b D x`, which is the value of
the inclusion on `x ⊗ d b`; so it defines a morphism `F ⟶ T` factoring `k`, uniquely because
the projection is epi. Exactness in the middle is then formal.

*What is missing, and what it needs.* The clause `Mono` of `ShortComplex.ShortExact` is not
proved here. It is the only clause whose proof needs the commutative-algebra sequence of
Tag 09CN, because it is the only one asserting that the symbol map loses no information, and
no argument from the universal properties of Tags 04BL and 09CT alone can see that: those
properties are about maps *out of* `Ω_{O₂/O₁}` and `P¹_{O₂/O₁}(F)`, whereas injectivity of
the inclusion is a statement about a map *into* `P¹_{O₂/O₁}(F)`. Concretely, it needs a
retraction of the inclusion, and the source of one is the first-order jet sheaf
`(Ω_{O₂/O₁} ⊗ F) ⊕ F` carrying the twisted action `b (ω, x) = (b ω + d b ⊗ x, b x)`, whose
universal operator `x ↦ (0, x)` has order at most one; the morphism out of
`P¹_{O₂/O₁}(F)` that Tag 09CT then supplies is the retraction. Identifying its composite
with the inclusion additionally needs that two morphisms out of `(Ω_{O₂/O₁} ⊗ F)^#` agreeing
on the sections `x ⊗ d b` agree, which is a genuine extra input: either the curried form of
the evaluation pairing, or Tag 08TP together with
`KaehlerDifferential.span_range_derivation`.

*Universes.* The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued, and the coefficient sheaves of modules live in
`SheafOfModules.{max u v w m}`. This is the variable block of Tags 04BL and 09CT and of
`principalPartsInclusion`, and it is forced rather than chosen there. The three generic
lemmas `evalTerminal_internalHomCompApp`, `evalTerminal_zero`, `tensorHom_eq_zero` and
`retraction_bracketCore_apply` are stated at one free module universe `t`; the universe
`max u v w m` is one instance of it. The abelian structure on `SheafOfModules.{max u v w m}`
that exactness needs is available from the hypotheses `HasWeakSheafify` and
`WEqualsLocallyBijective` that Tag 09CW supplies, through
`Stacks.instAbelianSheafOfModules`; no `HasSheafify` hypothesis and no smallness hypothesis
is added.

*Spelling.* `(Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj` and `Oforget O₂.obj` are
definitionally equal presheaves of rings but `CategoryTheory.sheafCompose` unfolds at neither
reducible nor instance transparency, so instance search cannot cross between them. Two
consequences. The `Zero` of the hom type
`PresheafOfModules.tensorObj F.val Ω.val ⟶ F.val` does **not** synthesize, because the source is
spelled over `Oforget O₂.obj` and the target over
`(Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj`; so `tensorHom_eq_zero` and
`eq_zero_of_adjunction_homEquiv_eq_zero` are stated generically, where there is one spelling, and
applied by `exact`, which is tolerant of definitional equality. For the same reason every identity
crossing the boundary below is discharged with `Eq.trans` and `congrArg` rather than with `rw`,
which refuses a goal that is not type-correct at the `implicit` transparency level.

*No tag.* Tag 09CW's content is the short exact sequence. Three of its four clauses are
proved here and `Mono` is not, so nothing in this file carries `@[stacks 09CW]`: a tag on a
partial statement would overstate the coverage.

## References

* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts.
* [Stacks Project, Tag 09CN](https://stacks.math.columbia.edu/tag/09CN), the
  commutative-algebra sequence of principal parts, and
  [Tag 08TP](https://stacks.math.columbia.edu/tag/08TP).
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials, and [Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), principal parts.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal hom.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

section Evaluation

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M P P' : PresheafOfModules.{t} (Oforget O)) (β : P ⟶ P')

/-- Post-composing a section of the internal hom with `β` post-composes its evaluation at
the terminal object of the slice site. -/
theorem evalTerminal_internalHomCompApp {X : Cᵒᵖ}
    (g : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) (a : M.obj X) :
    evalTerminal O M P'
        ((internalHomCompApp O M M P P' (𝟙 M) β X).hom g) a =
      (β.app X).hom (evalTerminal O M P g a) := by
  show (((restrFun O X.unop).map (𝟙 M) ≫ g ≫
    (restrFun O X.unop).map β).app (op (Over.mk (𝟙 X.unop)))).hom a = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The zero section of the internal hom evaluates to zero. -/
theorem evalTerminal_zero {X : Cᵒᵖ} (a : M.obj X) :
    evalTerminal O M P
      (0 : (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P) a = 0 := rfl

end Evaluation

section ZeroHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}

/-- The zero morphism of sheaves of modules is zero on sections. -/
theorem sheafHom_zero_val_app_apply {A B : _root_.SheafOfModules.{t} R} (X : Cᵒᵖ)
    (a : A.val.obj X) : ((0 : A ⟶ B).val.app X).hom a = 0 := rfl

/-- A vanishing morphism of sheaves of modules is zero on sections. -/
private theorem sheafHom_val_app_apply_eq_zero {A B : _root_.SheafOfModules.{t} R}
    {f : A ⟶ B} (hf : f = 0) (X : Cᵒᵖ) (a : A.val.obj X) : (f.val.app X).hom a = 0 := by
  subst hf
  exact sheafHom_zero_val_app_apply X a

end ZeroHom

section AdjunctionZero

/-- A morphism out of the image of a left adjoint vanishes as soon as its adjoint does.
The right adjoint is additive, so it carries the zero morphism to the zero morphism. -/
theorem eq_zero_of_adjunction_homEquiv_eq_zero {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {L : A ⥤ B} {Rt : B ⥤ A} (adj : L ⊣ Rt) [Rt.Additive]
    {X : A} {Y : B} (f : L.obj X ⟶ Y) (hf : adj.homEquiv X Y f = 0) : f = 0 := by
  have h0 : adj.homEquiv X Y 0 = 0 := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero, comp_zero]
  exact (adj.homEquiv X Y).injective (hf.trans h0.symm)

end AdjunctionZero

section TensorZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {M N P : PresheafOfModules.{t} (Oforget O)}

/-- **A morphism out of an objectwise tensor product vanishes as soon as it vanishes on pure
tensors.** -/
theorem tensorHom_eq_zero (uu : PresheafOfModules.tensorObj M N ⟶ P)
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X) (n : N.obj X),
      (uu.app X).hom (x ⊗ₜ[(Oforget O).obj X] n) = 0) : uu = 0 := by
  refine PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (TensorProduct.ext ?_)
  ext x n
  exact h X x n

end TensorZero

section BracketRetraction

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (M P : PresheafOfModules.{t} (Oforget O)) (D : ∀ X : Cᵒᵖ, M.obj X →+ P.obj X)
  (hbr : ∀ (X : Cᵒᵖ) (b r : O.obj X) (x : M.obj X),
    D X (b • r • x) - b • D X (r • x) = r • (D X (b • x) - b • D X x))
  (ρ : P ⟶ M) (hρ : ∀ (X : Cᵒᵖ) (x : M.obj X), (ρ.app X).hom (D X x) = x)

include hρ in
/-- **A retraction of `D` annihilates the commutators of `D`.** If `ρ` retracts the operator
`D`, then `ρ` carries `D (s x) - s D x` to `s x - s x = 0`. -/
theorem retraction_bracketCore_apply (X : Cᵒᵖ) (s : (Oforget O).obj X) (x : M.obj X) :
    (ρ.app X).hom ((bracketCore M P D hbr X s).hom x) = 0 := by
  have h : (ρ.app X).hom (s • D X x) = s • (ρ.app X).hom (D X x) :=
    (ρ.app X).hom.map_smul s (D X x)
  rw [bracketCore_apply, map_sub, h, hρ X (s • x), hρ X x, sub_self]

end BracketRetraction

section Composite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)
  (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- Post-composition with the projection `P¹_{O₂/O₁}(F) ⟶ F`, on the internal hom. -/
noncomputable def principalPartsPostcompRetraction :
    internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F) ⟶
      internalHomSheafOfModules F F :=
  ⟨internalHomComp O₂.obj F.val F.val (principalPartsOne.{v, u, w, m} φ F).val F.val
    (𝟙 F.val)
    (principalPartsRetraction.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val⟩

/-- **The symbol of the universal order-one operator is annihilated by the projection.**
In internal-hom form: the composite of the inclusion with post-composition by the
retraction `P¹_{O₂/O₁}(F) ⟶ F` is zero, because the retraction carries the commutator
`D (b x) - b D x` to `b x - b x = 0`. This is Tag 04BL's uniqueness applied to a morphism
out of `Ω_{O₂/O₁}` whose composite with the universal derivation vanishes. -/
theorem principalPartsInclusionHom_comp_postcompRetraction :
    principalPartsInclusionHom.{v, u, w, m} φ F ≫
        principalPartsPostcompRetraction.{v, u, w, m} φ F = 0 := by
  refine (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
      (0 : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
        internalHomSheafOfModules F F).val)).unique ?_ rfl
  ext X b
  refine Eq.trans (congrArg
    (fun z ↦ ((principalPartsPostcompRetraction.{v, u, w, m} φ F).val.app X).hom z)
    (principalPartsInclusionHom_d.{v, u, w, m} φ F X b)) ?_
  refine PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact retraction_bracketCore_apply F.val (principalPartsOne.{v, u, w, m} φ F).val
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1) _
    (principalPartsRetraction.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val
    (principalPartsRetraction_universalDiffOp.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1) (op V.unop.left) _ x

/-- The presheaf-level symbol, evaluated on a pure tensor, is annihilated by the
retraction. -/
theorem retraction_principalPartsPairingPresheaf_tmul (X : Cᵒᵖ) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    ((principalPartsRetraction.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1).val.app X).hom
        (((principalPartsPairingPresheaf.{v, u, w, m} φ F).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X] ω)) = 0 := by
  have hz : ((internalHomCompApp O₂.obj F.val F.val
        (principalPartsOne.{v, u, w, m} φ F).val F.val (𝟙 F.val)
        (principalPartsRetraction.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) F 1).val X).hom
      (((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom ω)) = 0 :=
    sheafHom_val_app_apply_eq_zero
      (principalPartsInclusionHom_comp_postcompRetraction.{v, u, w, m} φ F) X ω
  refine Eq.trans (congrArg
    (fun z ↦ ((principalPartsRetraction.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1).val.app X).hom z)
    (principalPartsPairingPresheaf_tmul.{v, u, w, m} φ F X x ω)) ?_
  refine Eq.trans (evalTerminal_internalHomCompApp O₂.obj F.val
    (principalPartsOne.{v, u, w, m} φ F).val F.val
    (principalPartsRetraction.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1).val
    (((principalPartsInclusionHom.{v, u, w, m} φ F).val.app X).hom ω) x).symm ?_
  exact Eq.trans (congrArg
    (fun g : (restrFun O₂.obj X.unop).obj F.val ⟶ (restrFun O₂.obj X.unop).obj F.val ↦
      evalTerminal O₂.obj F.val F.val (X := X) g x) hz)
    (evalTerminal_zero O₂.obj F.val F.val x)

end Composite

section Sequence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)
  (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- **The sequence of principal parts is a complex**: the composite of the inclusion
`Ω_{O₂/O₁} ⊗ F ⟶ P¹_{O₂/O₁}(F)` with the projection `P¹_{O₂/O₁}(F) ⟶ F` vanishes. -/
theorem principalPartsInclusion_comp_projection :
    (principalPartsInclusion.{v, u, w, m} φ).app F ≫
        (principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F = 0 := by
  let : (_root_.SheafOfModules.forget.{max u v w m}
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).Additive :=
    _root_.SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget _
  refine eq_zero_of_adjunction_homEquiv_eq_zero
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)) _ ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) ?_
  refine Eq.trans (congrArg (fun g ↦ g ≫
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).map
        ((principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F))
    (Equiv.apply_symm_apply ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv
      (PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val)
      (principalPartsOne.{v, u, w, m} φ F))
      (principalPartsPairingPresheaf.{v, u, w, m} φ F))) ?_
  exact tensorHom_eq_zero _
    (retraction_principalPartsPairingPresheaf_tmul.{v, u, w, m} φ F)

/-- **The projection of the sequence of principal parts is an epimorphism.** The universal
operator of order at most one is a section of it on local sections, so it is surjective on
sections, hence locally surjective, hence epi. -/
instance epi_principalPartsProjection_app :
    Epi ((principalPartsProjection.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) 1).app F) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (Presheaf.isLocallySurjective_of_surjective J _ fun X y ↦
      ⟨universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X y,
        principalPartsProjection_universalDiffOp.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1 F X y⟩)

variable {T : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
  (k : principalPartsOne.{v, u, w, m} φ F ⟶ T)
  (hk : (principalPartsInclusion.{v, u, w, m} φ).app F ≫ k = 0)

include hk in
/-- **A morphism annihilating the inclusion makes the universal operator linear.** The
commutator `D (b x) - b D x` is the value of the inclusion on `x ⊗ d b`, so a morphism
killing the inclusion turns the universal operator into an `O₂`-linear map. -/
theorem map_smul_comp_universalDiffOp (X : Cᵒᵖ)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) (x : F.val.obj X) :
    (k.val.app X).hom
        (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x)) =
      b • (k.val.app X).hom
        (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x) := by
  have h1 : (k.val.app X).hom
      ((((principalPartsInclusion.{v, u, w, m} φ).app F).val.app X).hom
        (((toSheafify J (PresheafOfModules.tensorObj F.val
            (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).presheaf).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b))) = 0 :=
    sheafHom_val_app_apply_eq_zero hk X _
  have h2 := congrArg (fun z ↦ (k.val.app X).hom z)
    (principalPartsInclusion_toSheafify_tmul_d.{v, u, w, m} φ F X x b)
  have h4 : (k.val.app X).hom
        (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x) -
          b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x) =
      (k.val.app X).hom
          (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x)) -
        b • (k.val.app X).hom
          (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x) := by
    rw [map_sub, (k.val.app X).hom.map_smul]
  exact sub_eq_zero.mp (h4.symm.trans (h2.symm.trans h1))

include hk in
/-- **The factorization of a morphism annihilating the inclusion through the projection.**
Its value on local sections is `x ↦ k (D x)`, which is `O₂`-linear because `k` kills the
inclusion, and natural because a differential operator is compatible with restriction. -/
noncomputable def descPrincipalParts : F ⟶ T :=
  ⟨{ app X := ModuleCat.ofHom
       { toFun x := (k.val.app X).hom
           (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x)
         map_add' x y := by
           refine Eq.trans (congrArg (fun z ↦ (k.val.app X).hom z)
             (map_add (universalDiffOp.{v, u, w, m}
               (underlyingRingSheafMapOfSite φ) F 1 X) x y)) ?_
           exact map_add _ _ _
         map_smul' b x := map_smul_comp_universalDiffOp.{v, u, w, m} φ F k hk X b x }
     naturality := by
       intro X Y f
       refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
       refine Eq.trans (congrArg (fun z ↦ (k.val.app Y).hom z)
         (globalDiffOp_naturality _ (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
           (underlyingRingSheafMapOfSite φ) F 1) f x)) ?_
       exact PresheafOfModules.naturality_apply k.val f _ }⟩

include hk in
/-- The factorization is a factorization: composing it with the projection recovers `k`. -/
theorem projection_comp_descPrincipalParts :
    (principalPartsProjection.{v, u, w, m} (underlyingRingSheafMapOfSite φ) 1).app F ≫
        descPrincipalParts.{v, u, w, m} φ F k hk = k := by
  refine (existsUnique_descDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F T 1
    (postcomp (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1) k)
    (postcomp_isDiffOpOfOrder (underlyingRingSheafMapOfSite φ) 1 _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) k)).unique ?_ rfl
  funext X
  exact AddMonoidHom.ext fun x ↦
    congrArg (fun z ↦ ((descPrincipalParts.{v, u, w, m} φ F k hk).val.app X).hom z)
      (principalPartsProjection_universalDiffOp.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) 1 F X x)

/-- **The projection is a cokernel of the inclusion.** Given a morphism out of
`P¹_{O₂/O₁}(F)` annihilating the inclusion, the composite with the universal operator is
`O₂`-linear and factors it through `F`, uniquely because the projection is epi. -/
noncomputable def isColimitCokernelCoforkPrincipalParts :
    IsColimit (CokernelCofork.ofπ
      ((principalPartsProjection.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) 1).app F)
      (principalPartsInclusion_comp_projection.{v, u, w, m} φ F)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} g hg ↦
    ⟨descPrincipalParts.{v, u, w, m} φ F g hg,
      projection_comp_descPrincipalParts.{v, u, w, m} φ F g hg⟩

/-- **The sequence of principal parts is exact in the middle.** -/
@[sga "6 II AppII.1.2.4" "partial"]
theorem shortComplex_exact_principalParts :
    (ShortComplex.mk ((principalPartsInclusion.{v, u, w, m} φ).app F)
      ((principalPartsProjection.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) 1).app F)
      (principalPartsInclusion_comp_projection.{v, u, w, m} φ F)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkPrincipalParts.{v, u, w, m} φ F)

/-- **Tag 09CW's short-exactness clause, modulo the one clause this file does not prove.**
Granted that the inclusion is a monomorphism, the sequence of principal parts is a short
exact sequence, in exactly the form Tag 09CW asks for. The hypothesis is an instance
argument so that this reads as the precise residual obligation; see the implementation
notes for what proving it needs. -/
theorem exists_shortExact_principalPartsSequence
    [Mono ((principalPartsInclusion.{v, u, w, m} φ).app F)] :
    ∃ h : (principalPartsInclusion.{v, u, w, m} φ).app F ≫
        (principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F = 0,
      (ShortComplex.mk ((principalPartsInclusion.{v, u, w, m} φ).app F)
        ((principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F) h).ShortExact :=
  ⟨principalPartsInclusion_comp_projection.{v, u, w, m} φ F,
    ShortComplex.ShortExact.mk' (shortComplex_exact_principalParts.{v, u, w, m} φ F)
      inferInstance inferInstance⟩

end Sequence

end AlgebraicGeometry.SheafOfModules

end
