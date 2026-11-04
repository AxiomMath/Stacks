module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsFunctorial
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsPairing
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the sequence of principal parts in a square of sheaves of rings

Let
```
A ──φ──▸ B
│         │
α         β
▼         ▼
A' ─φ'─▸ B'
```
be a commutative square of sheaves of commutative rings on a site, let `F` be a sheaf of
`B`-modules, let `F'` be a sheaf of `B'`-modules and let `uF : F ⟶ β^*F'` be a `B`-linear map.
The sequence of first principal parts of Tag 09CW,

`0 ⟶ Ω_{B/A} ⊗_B F ⟶ P¹_{B/A}(F) ⟶ F ⟶ 0`,

is natural for such data: with the middle arrow the change-of-rings map of Tag 09CX, the right
arrow `uF` and the left arrow the objectwise tensor product of `uF` with the canonical map
`Ω_{B/A} ⟶ β^*Ω_{B'/A'}` of Tag 08TR, both squares commute.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.tensorRestrictScalars`: the comparison map
  `β^*M ⊗_B β^*N ⟶ β^*(M ⊗_{B'} N)` of objectwise tensor products of presheaves of modules.
* `AlgebraicGeometry.SheafOfModules.internalHomRestrictScalars`: the comparison map
  `β^*𝓗om_{B'}(M, P) ⟶ 𝓗om_B(β^*M, β^*P)` of internal homs.
* `AlgebraicGeometry.SheafOfModules.underlyingRingSquare`: the square of underlying sheaves of
  rings, which is what the change-of-rings map of Tag 09CX is stated for.
* `AlgebraicGeometry.SheafOfModules.principalPartsSquareMap`: **the middle arrow**, the
  change-of-rings map of Tag 09CX in order one, read over sheaves of *commutative* rings.
* `AlgebraicGeometry.SheafOfModules.differentialsTensorMap`: **the left arrow**, the sheafified
  tensor product of `uF` with the canonical map on relative differentials.

## Main results

* `AlgebraicGeometry.SheafOfModules.principalPartsSequence_naturality_projection` and
  `AlgebraicGeometry.SheafOfModules.principalPartsSequence_naturality_inclusion`: **the two
  squares**, which together say that the change-of-rings maps on principal parts are compatible
  with the short exact sequences of Tag 09CW.

## Implementation notes

The change-of-rings map `principalPartsMapOfSquare` is stated for a square of sheaves of
(possibly noncommutative) rings, while the sequence of Tag 09CW is stated for sheaves of
commutative rings; `underlyingRingSquare` is the transport of the square through
`CategoryTheory.sheafCompose J (forget₂ CommRingCat RingCat)` that lets the two meet.

The projection square is a statement about two morphisms out of `P¹_{B/A}(F)`, which
corepresents the differential operators of order at most one out of `F`, so it is settled by
evaluating both sides on the universal operator: there
`AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare_universalOperator` and
`AlgebraicGeometry.SheafOfModules.principalPartsProjection_universalDiffOp` compute everything.
This is the strategy of `principalPartsMapOfSquare_comp_orderReduction`.

The inclusion square cannot be settled that way: its two sides are morphisms out of the
sheafified tensor product `Ω_{B/A} ⊗_B F`, whose sections are not generated objectwise by the
differentials `d b`. What replaces the computation is the universal property of `Ω_{B/A}` itself
(Tag 04BL). Through the sheafification adjunction and the evaluation pairing of
`PrincipalPartsPairing.lean`, both sides are induced by morphisms
`Ω_{B/A} ⟶ 𝓗om_B(F, β^*P¹_{B'/A'}(F'))`, and that internal hom is a sheaf of modules by
Tag 03EM, so two such morphisms agree as soon as they carry every `d b` to the same section.
Both carry `d b` to the commutator of `b` with the operator `D'_{F'} ∘ uF` — the very operator
whose factorisation is `principalPartsMapOfSquare` — so they agree; that is
`principalPartsInclusionHom_square`.

Two comparison maps are needed to make that argument expressible, because the primed half of the
diagram lives over `B'` while the diagram itself lives over `B`: one for the objectwise tensor
product and one for the internal hom. Both are the identity on local sections and carry no
content beyond the change of the acting ring, so they are stated for an arbitrary morphism of
the underlying presheaves of rings.

Spelling. `(Stacks.SheafOfModules.Tensor.ringSheaf O).obj` and `Oforget O.obj` are definitionally
equal presheaves of rings, but `CategoryTheory.sheafCompose` unfolds at neither reducible nor
instance transparency, so instance search cannot cross between them and no transparency option is
set here. The devices are those of `PrincipalPartsPairing.lean`: a scalar or a section that has to
be read in the `Oforget` spelling is bound there by a `let` whose type says so, the module
structures needed in that spelling are supplied as local instances, and the identities between
spellings are discharged by `exact` and `congrArg`, which are checked up to definitional equality,
never by `rw` or `simp`.

Universes. The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued and coefficient modules live in `SheafOfModules.{max u v w m}` for a
free `m`, which is the universe in which Tags 04BL and 09CT are corepresentable and in which
Tag 03EM's internal hom closes up. Nothing is narrowed: `u`, `v`, `w`, `m` are free and the
site is not assumed small.

## References

* [Stacks Project, Tag 09CX](https://stacks.math.columbia.edu/tag/09CX)
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the short exact
  sequence of first principal parts.
* [Stacks Project, Tag 08TR](https://stacks.math.columbia.edu/tag/08TR), functoriality of
  relative differentials, and [Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), their
  universal property.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal hom of
  sheaves of modules is a sheaf.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

section RestrictScalarsComparison

variable {C : Type u} [Category.{v} C] {O O' : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The comparison map `β^*M ⊗_O β^*N ⟶ β^*(M ⊗_{O'} N)` of objectwise tensor products, at one
object of the site: a pure tensor over `O(X)` goes to the pure tensor of the same two sections
over `O'(X)`. -/
noncomputable def tensorRestrictScalarsApp (g : ringPresheaf O ⟶ ringPresheaf O')
    (M N : _root_.PresheafOfModules.{t} (ringPresheaf O')) (X : Cᵒᵖ) :
    (PresheafOfModules.tensorObj (O := O)
        ((_root_.PresheafOfModules.restrictScalars g).obj M)
        ((_root_.PresheafOfModules.restrictScalars g).obj N)).obj X ⟶
      ((_root_.PresheafOfModules.restrictScalars g).obj
        (PresheafOfModules.tensorObj (O := O') M N)).obj X := by
  let T := ((_root_.PresheafOfModules.restrictScalars g).obj
    (PresheafOfModules.tensorObj (O := O') M N)).obj X
  letI : Module ((ringPresheaf O).obj X) T := T.isModule
  let pair := TensorProduct.mk ((ringPresheaf O').obj X) (M.obj X) (N.obj X)
  let bil : (((_root_.PresheafOfModules.restrictScalars g).obj M).obj X)
      →ₗ[(ringPresheaf O).obj X]
      (((_root_.PresheafOfModules.restrictScalars g).obj N).obj X)
        →ₗ[(ringPresheaf O).obj X] T :=
    { toFun := fun a ↦
        { toFun := fun b ↦ pair a b
          map_add' := fun b b' ↦ (pair a).map_add b b'
          map_smul' := fun r b ↦ (pair a).map_smul ((g.app X).hom r) b }
      map_add' := fun a a' ↦ LinearMap.ext fun b ↦ LinearMap.congr_fun (pair.map_add a a') b
      map_smul' := fun r a ↦ LinearMap.ext fun b ↦
        LinearMap.congr_fun (pair.map_smul ((g.app X).hom r) a) b }
  exact ConcreteCategory.ofHom (TensorProduct.lift bil)

/-- **The comparison map `β^*M ⊗_O β^*N ⟶ β^*(M ⊗_{O'} N)`** of objectwise tensor products of
presheaves of modules, attached to a morphism `g : O ⟶ O'` of the underlying presheaves of
rings. -/
noncomputable def tensorRestrictScalars (g : ringPresheaf O ⟶ ringPresheaf O')
    (M N : _root_.PresheafOfModules.{t} (ringPresheaf O')) :
    PresheafOfModules.tensorObj (O := O)
        ((_root_.PresheafOfModules.restrictScalars g).obj M)
        ((_root_.PresheafOfModules.restrictScalars g).obj N) ⟶
      (_root_.PresheafOfModules.restrictScalars g).obj
        (PresheafOfModules.tensorObj (O := O') M N) where
  app X := tensorRestrictScalarsApp g M N X
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a b
    rfl

/-- A morphism `M|_U ⟶ P|_U` of presheaves of modules on the slice site over `U`, read over the
smaller ring: the same maps on sections, linear over `O` rather than over `O'`. -/
noncomputable def restrictHomSlice (g : Oforget O ⟶ Oforget O')
    (M P : _root_.PresheafOfModules.{t} (Oforget O')) (U : C)
    (h : (restrFun O' U).obj M ⟶ (restrFun O' U).obj P) :
    (restrFun O U).obj ((_root_.PresheafOfModules.restrictScalars g).obj M) ⟶
      (restrFun O U).obj ((_root_.PresheafOfModules.restrictScalars g).obj P) where
  app V := (ModuleCat.restrictScalars (g.app (op V.unop.left)).hom).map (h.app V)
  naturality {V W} q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact _root_.PresheafOfModules.naturality_apply h q x

/-- The comparison map `β^*𝓗om_{O'}(M, P) ⟶ 𝓗om_O(β^*M, β^*P)` of internal homs, at one object
of the site. -/
noncomputable def internalHomRestrictScalarsApp (g : Oforget O ⟶ Oforget O')
    (M P : _root_.PresheafOfModules.{t} (Oforget O')) (X : Cᵒᵖ) :
    ((_root_.PresheafOfModules.restrictScalars g).obj (internalHom O' M P)).obj X ⟶
      (internalHom O ((_root_.PresheafOfModules.restrictScalars g).obj M)
        ((_root_.PresheafOfModules.restrictScalars g).obj P)).obj X :=
  ModuleCat.homAddEquiv.symm
    { toFun := fun h ↦ restrictHomSlice g M P X.unop h
      map_add' := fun h h' ↦ by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl
      map_smul' := fun r h ↦ by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hnat : fRestr O' X.unop ((g.app X).hom r) V
            = (g.app (op V.unop.left)).hom (fRestr O X.unop r V) :=
          congrArg (fun q : (Oforget O).obj X ⟶ (Oforget O').obj (op V.unop.left) ↦ q.hom r)
            (g.naturality V.unop.hom.op).symm
        exact congrArg (fun s : (Oforget O').obj (op V.unop.left) ↦
          s • (show P.obj (op V.unop.left) from (h.app V).hom x)) hnat }

/-- **The comparison map `β^*𝓗om_{O'}(M, P) ⟶ 𝓗om_O(β^*M, β^*P)`** of internal homs, attached
to a morphism `g : O ⟶ O'` of the underlying presheaves of rings. It is the identity on local
sections; only the acting ring changes. -/
noncomputable def internalHomRestrictScalars (g : Oforget O ⟶ Oforget O')
    (M P : _root_.PresheafOfModules.{t} (Oforget O')) :
    (_root_.PresheafOfModules.restrictScalars g).obj (internalHom O' M P) ⟶
      internalHom O ((_root_.PresheafOfModules.restrictScalars g).obj M)
        ((_root_.PresheafOfModules.restrictScalars g).obj P) where
  app X := internalHomRestrictScalarsApp g M P X
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply _root_.PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end RestrictScalarsComparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}

/-- The square of underlying sheaves of rings attached to a commutative square of sheaves of
commutative rings. -/
theorem underlyingRingSquare (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (hsq : φ ≫ β = α ≫ φ') :
    underlyingRingSheafMapOfSite φ ≫ underlyingRingSheafMapOfSite β =
      underlyingRingSheafMapOfSite α ≫ underlyingRingSheafMapOfSite φ' :=
  (((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp φ β).symm.trans
    (congrArg (fun h : O₁ ⟶ O₂' ↦
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map h) hsq)).trans
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp α φ')

/-- **The middle arrow** of the naturality diagram: the change-of-rings map of Tag 09CX on
first principal parts, for a square of sheaves of commutative rings. -/
noncomputable abbrev principalPartsSquareMap (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁')
    (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 ⟶
      (_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1) :=
  principalPartsMapOfSquare.{v, u, w, m} (underlyingRingSheafMapOfSite φ)
    (underlyingRingSheafMapOfSite φ') (underlyingRingSheafMapOfSite α)
    (underlyingRingSheafMapOfSite β) (underlyingRingSquare φ φ' α β hsq) F F' uF 1

/-- The change-of-rings map on first principal parts sends the universal operator at `s` to the
universal operator at `uF s`. -/
private theorem principalPartsSquareMap_universalDiffOp
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') (X : Cᵒᵖ) (s : F.val.obj X) :
    ((principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF).val.app X).hom
        (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X s) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1 X
        ((uF.val.app X).hom s) :=
  principalPartsMapOfSquare_universalOperator (underlyingRingSheafMapOfSite φ)
    (underlyingRingSheafMapOfSite φ') (underlyingRingSheafMapOfSite α)
    (underlyingRingSheafMapOfSite β) (underlyingRingSquare φ φ' α β hsq) F F' uF 1 X s

/-- **Stacks 09CX.** The change-of-rings maps on first principal parts are compatible with the
projections of the short exact sequences of Tag 09CW: the right-hand square of the naturality
diagram commutes, the comparison of its two right-hand terms being `uF`. -/
@[stacks 09CX "sequence naturality: the projection square"]
theorem principalPartsSequence_naturality_projection
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF ≫
        (_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).map
          ((principalPartsProjection.{v, u, w, m}
            (underlyingRingSheafMapOfSite φ') 1).app F') =
      (principalPartsProjection.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) 1).app F ≫ uF := by
  let T := differentialOperatorsFunctor.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1
  let f := principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF ≫
    (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).map
      ((principalPartsProjection.{v, u, w, m} (underlyingRingSheafMapOfSite φ') 1).app F')
  let g := (principalPartsProjection.{v, u, w, m}
    (underlyingRingSheafMapOfSite φ) 1).app F ≫ uF
  apply T.corepresentableBy.homEquiv.injective
  rw [T.corepresentableBy.homEquiv_eq f, T.corepresentableBy.homEquiv_eq g]
  apply Subtype.ext
  funext X
  ext s
  change (((principalPartsProjection _ 1).app F').val.app X).hom
      (((principalPartsSquareMap φ φ' α β hsq F F' uF).val.app X).hom
        (universalDiffOp _ F 1 X s)) =
    (uF.val.app X).hom ((((principalPartsProjection _ 1).app F).val.app X).hom
      (universalDiffOp _ F 1 X s))
  rw [principalPartsSquareMap_universalDiffOp, principalPartsProjection_universalDiffOp]
  erw [principalPartsProjection_universalDiffOp]

section Inclusion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]
  {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}

/-- **The inclusion of the sequence of principal parts is the sheafification of the evaluation
pairing**, on every local section of the objectwise tensor product. This is
`principalPartsInclusionApp_toSheafify_tmul_d` with the pairing left unevaluated, which is what
makes it usable at an arbitrary local section of `Ω_{O₂/O₁}` rather than only at a
differential. -/
theorem principalPartsInclusion_toSheafify (φ : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) (X : Cᵒᵖ)
    (y : (PresheafOfModules.tensorObj (O := O₂.obj) F.val
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).obj X) :
    (((principalPartsInclusion.{v, u, w, m} φ).app F).val.app X).hom
        (((toSheafify J (PresheafOfModules.tensorObj F.val
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).presheaf).app X).hom y) =
      ((principalPartsPairingPresheaf.{v, u, w, m} φ F).app X).hom y := by
  have h := _root_.PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
    (principalPartsInclusionApp.{v, u, w, m} φ F)
  rw [show _root_.PresheafOfModules.sheafificationHomEquiv
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
        (principalPartsInclusionApp.{v, u, w, m} φ F) =
      principalPartsPairingPresheaf.{v, u, w, m} φ F from
    Equiv.apply_symm_apply ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv
      (PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val)
      (principalPartsOne.{v, u, w, m} φ F))
      (principalPartsPairingPresheaf.{v, u, w, m} φ F)] at h
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h X) y).symm

/-- The universal differential operator of order at most one out of `F'`, precomposed with the
module map `uF`: an operator out of `F` with values in `β^*P¹_{B'/A'}(F')`. This is the operator
whose factorisation through the universal one is the change-of-rings map on principal parts. -/
noncomputable def precompUniversalDiffOp (φ' : O₁' ⟶ O₂') (β : O₂ ⟶ O₂')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    DiffOp.GlobalOp F ((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj (principalPartsOne.{v, u, w, m} φ' F')) :=
  fun X ↦ (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1 X).comp
    ((uF.val.app X).hom.toAddMonoidHom)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- `precompUniversalDiffOp` is a differential operator of order at most one. -/
theorem precompUniversalDiffOp_isGlobalDiffOpOfOrder
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    DiffOp.IsGlobalDiffOpOfOrder (underlyingRingSheafMapOfSite φ) 1
      (precompUniversalDiffOp.{v, u, w, m} φ' β F F' uF) := by
  intro U
  change DiffOp.IsDiffOpOfOrder (underlyingRingSheafMapOfSite φ) 1
    (precompRaw.{v, u, w, m} (underlyingRingSheafMapOfSite β) F F' uF
      ((universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1).restrict U))
  exact isDiffOpOfOrder_precompRaw.{v, u, w, m}
    (φ := underlyingRingSheafMapOfSite φ) (φ' := underlyingRingSheafMapOfSite φ')
    (β := underlyingRingSheafMapOfSite β) (F := F) (F' := F') (k := 1)
    (α := underlyingRingSheafMapOfSite α) (h := underlyingRingSquare φ φ' α β hsq) uF
    ((universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1).restrict U)
    (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ') F' 1 U)

/-- The symbol of `precompUniversalDiffOp`, as a relative derivation with values in the internal
hom `𝓗om_B(F, β^*P¹_{B'/A'}(F'))`: it carries a section `b` to the commutator
`x ↦ D'(β(b)·uF x) - β(b)·D'(uF x)`. -/
noncomputable def crossSymbolDerivation
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    (internalHomSheafOfModules F
        ((_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).obj
          (principalPartsOne.{v, u, w, m} φ' F'))).val.Derivation' φ.hom :=
  internalHomDerivation φ.hom F.val
    ((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj (principalPartsOne.{v, u, w, m} φ' F')).val
    (precompUniversalDiffOp.{v, u, w, m} φ' β F F' uF)
    (fun X b r x ↦ isGlobalDiffOpOfOrder_one_bracket _
      (precompUniversalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m} φ φ' α β hsq F F' uF) X b r x)
    (fun {_ _} f x ↦ globalDiffOp_naturality _
      (precompUniversalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m} φ φ' α β hsq F F' uF) f x)
    (fun X a x ↦ isGlobalDiffOpOfOrder_one_base _
      (precompUniversalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m} φ φ' α β hsq F F' uF) X a x)

/-- Post-composition with the change-of-rings map on principal parts, on the internal hom out
of `F`. -/
noncomputable def principalPartsSquarePostcomp
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    internalHomSheafOfModules F (principalPartsOne.{v, u, w, m} φ F) ⟶
      internalHomSheafOfModules F
        ((_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).obj
          (principalPartsOne.{v, u, w, m} φ' F')) :=
  ⟨internalHomComp O₂.obj F.val F.val (principalPartsOne.{v, u, w, m} φ F).val
    ((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj
      (principalPartsOne.{v, u, w, m} φ' F')).val (𝟙 _)
    (principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF).val⟩

/-- Restriction of scalars along `β` followed by precomposition with `uF`, on the internal hom
of the primed data. -/
noncomputable def crossPrecomp (φ' : O₁' ⟶ O₂') (β : O₂ ⟶ O₂')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    (_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (internalHomSheafOfModules F' (principalPartsOne.{v, u, w, m} φ' F')) ⟶
      internalHomSheafOfModules F
        ((_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).obj
          (principalPartsOne.{v, u, w, m} φ' F')) :=
  ⟨internalHomRestrictScalars (underlyingRingSheafMapOfSite β).hom F'.val
      (principalPartsOne.{v, u, w, m} φ' F').val ≫
    internalHomComp O₂.obj F.val
      ((_root_.PresheafOfModules.restrictScalars
        (underlyingRingSheafMapOfSite β).hom).obj F'.val)
      ((_root_.PresheafOfModules.restrictScalars
        (underlyingRingSheafMapOfSite β).hom).obj
        (principalPartsOne.{v, u, w, m} φ' F').val)
      ((_root_.PresheafOfModules.restrictScalars
        (underlyingRingSheafMapOfSite β).hom).obj
        (principalPartsOne.{v, u, w, m} φ' F').val)
      uF.val (𝟙 _)⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- The canonical map on relative differentials carries the universal differential of `b` to the
universal differential of `β(b)`. -/
theorem mapDifferentials_universalDerivation
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (X : Cᵒᵖ) (b : O₂.obj.obj X) :
    (((mapDifferentials.{v, u, w, m} φ φ' α β hsq).val.app X)).hom
        ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b) =
      (universalDerivationOfSite.{v, u, w, m} O₁' O₂' φ').d (β.hom.app X b) :=
  (_root_.PresheafOfModules.Derivation.congr_d
    (functorialDifferentials.{v, u, w, m} φ φ' α β hsq).fac b).trans
    ((functorialDifferentials.{v, u, w, m} φ φ' α β hsq).inducedDerivation_apply X b)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- The derivation induced by `principalPartsInclusionHom` followed by
`principalPartsSquarePostcomp` is `crossSymbolDerivation`. -/
private theorem postcomp_principalPartsInclusionHom_comp_principalPartsSquarePostcomp
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
        (principalPartsInclusionHom.{v, u, w, m} φ F ≫
          principalPartsSquarePostcomp.{v, u, w, m} φ φ' α β hsq F F' uF).val =
      crossSymbolDerivation.{v, u, w, m} φ φ' α β hsq F F' uF := by
  ext X b
  refine Eq.trans (congrArg
    (fun z ↦ ((principalPartsSquarePostcomp.{v, u, w, m}
      φ φ' α β hsq F F' uF).val.app X).hom z)
    (principalPartsInclusionHom_d.{v, u, w, m} φ F X b)) ?_
  refine _root_.PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  let r : (Oforget O₂.obj).obj (op V.unop.left) := fRestr O₂.obj X.unop b V
  let x₀ : F.val.obj (op V.unop.left) := x
  let _ : Module ((Oforget O₂.obj).obj (op V.unop.left))
      (((_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (principalPartsOne.{v, u, w, m} φ' F')).val.obj (op V.unop.left)) :=
    (((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj
      (principalPartsOne.{v, u, w, m} φ' F')).val.obj (op V.unop.left)).isModule
  let _ : Module ((Oforget O₂.obj).obj (op V.unop.left))
      (F.val.obj (op V.unop.left)) := (F.val.obj (op V.unop.left)).isModule
  let _ : Module ((Oforget O₂.obj).obj (op V.unop.left))
      ((principalPartsOne.{v, u, w, m} φ F).val.obj (op V.unop.left)) :=
    ((principalPartsOne.{v, u, w, m} φ F).val.obj (op V.unop.left)).isModule
  have h1 := principalPartsSquareMap_universalDiffOp.{v, u, w, m} φ φ' α β hsq F F' uF
    (op V.unop.left) (r • x₀)
  have h2 := principalPartsSquareMap_universalDiffOp.{v, u, w, m} φ φ' α β hsq F F' uF
    (op V.unop.left) x₀
  have hsm := ((principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF).val.app
      (op V.unop.left)).hom.map_smul r
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1
      (op V.unop.left) x₀)
  have hsub := map_sub ((principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF).val.app
      (op V.unop.left)).hom
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 (op V.unop.left)
      (r • x₀))
    (r • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1
      (op V.unop.left) x)
  exact hsub.trans (congrArg₂ (fun y z ↦ y - z) h1
    (hsm.trans (congrArg (fun z ↦ r • z) h2)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- The derivation induced by `mapDifferentials` followed by the inclusion of principal parts
and `crossPrecomp` is `crossSymbolDerivation`. -/
private theorem postcomp_mapDifferentials_comp_crossPrecomp
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
        (mapDifferentials.{v, u, w, m} φ φ' α β hsq ≫
          (_root_.SheafOfModules.restrictScalars.{max u v w m}
            (underlyingRingSheafMapOfSite β)).map
            (principalPartsInclusionHom.{v, u, w, m} φ' F') ≫
            crossPrecomp.{v, u, w, m} φ' β F F' uF).val =
      crossSymbolDerivation.{v, u, w, m} φ φ' α β hsq F F' uF := by
  ext X b
  refine Eq.trans (congrArg
    (fun z ↦ ((crossPrecomp.{v, u, w, m} φ' β F F' uF).val.app X).hom
      (((principalPartsInclusionHom.{v, u, w, m} φ' F').val.app X).hom z))
    (mapDifferentials_universalDerivation.{v, u, w, m} φ φ' α β hsq X b)) ?_
  refine Eq.trans (congrArg
    (fun z ↦ ((crossPrecomp.{v, u, w, m} φ' β F F' uF).val.app X).hom z)
    (principalPartsInclusionHom_d.{v, u, w, m} φ' F' X (β.hom.app X b))) ?_
  refine _root_.PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  let _ : Module ((Oforget O₂'.obj).obj (op V.unop.left))
      (F'.val.obj (op V.unop.left)) := (F'.val.obj (op V.unop.left)).isModule
  let _ : Module ((Oforget O₂'.obj).obj (op V.unop.left))
      ((principalPartsOne.{v, u, w, m} φ' F').val.obj (op V.unop.left)) :=
    ((principalPartsOne.{v, u, w, m} φ' F').val.obj (op V.unop.left)).isModule
  let _ : Module ((Oforget O₂.obj).obj (op V.unop.left))
      (F.val.obj (op V.unop.left)) := (F.val.obj (op V.unop.left)).isModule
  let r : (Oforget O₂.obj).obj (op V.unop.left) := fRestr O₂.obj X.unop b V
  let x₀ : F.val.obj (op V.unop.left) := x
  let s : (Oforget O₂'.obj).obj (op V.unop.left) :=
    fRestr O₂'.obj X.unop (β.hom.app X b) V
  let s' : (Oforget O₂'.obj).obj (op V.unop.left) :=
    (β.hom.app (op V.unop.left)).hom (fRestr O₂.obj X.unop b V)
  let y : F'.val.obj (op V.unop.left) := (uF.val.app (op V.unop.left)).hom x
  have hnat : s = s' :=
    congrArg (fun q : O₂.obj.obj X ⟶ O₂'.obj.obj (op V.unop.left) ↦ q.hom b)
      (β.hom.naturality V.unop.hom.op).symm
  have hu : (uF.val.app (op V.unop.left)).hom (r • x₀) = s' • y :=
    (uF.val.app (op V.unop.left)).hom.map_smul r x₀
  exact congrArg₂ (fun z z' ↦ z - z')
    ((congrArg (fun c : (Oforget O₂'.obj).obj (op V.unop.left) ↦
        universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1
          (op V.unop.left) (c • y)) hnat).trans
      (congrArg (fun z : F'.val.obj (op V.unop.left) ↦
        universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1
          (op V.unop.left) z) hu).symm)
    (congrArg (fun c : (Oforget O₂'.obj).obj (op V.unop.left) ↦
      c • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ') F' 1
        (op V.unop.left) y) hnat)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}] in
/-- **The two internal-hom forms of the left-hand square agree.** Both sides are morphisms out
of `Ω_{B/A}` and both carry a differential `d b` to the commutator of `b` with the operator
`D'_{F'} ∘ uF`, so the universal property of `Ω_{B/A}` (Tag 04BL) identifies them. -/
theorem principalPartsInclusionHom_square
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    principalPartsInclusionHom.{v, u, w, m} φ F ≫
        principalPartsSquarePostcomp.{v, u, w, m} φ φ' α β hsq F F' uF =
      mapDifferentials.{v, u, w, m} φ φ' α β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).map
          (principalPartsInclusionHom.{v, u, w, m} φ' F') ≫
          crossPrecomp.{v, u, w, m} φ' β F F' uF :=
  (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    (crossSymbolDerivation.{v, u, w, m} φ φ' α β hsq F F' uF)).unique
    (postcomp_principalPartsInclusionHom_comp_principalPartsSquarePostcomp.{v, u, w, m}
      φ φ' α β hsq F F' uF)
    (postcomp_mapDifferentials_comp_crossPrecomp.{v, u, w, m} φ φ' α β hsq F F' uF)

/-- The map from the objectwise tensor product `F ⊗ Ω_{O₂/O₁}` to its sheafification, as a
morphism of presheaves of modules: the unit of the sheafification adjunction. -/
noncomputable def tensorSheafifyUnit (φ : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    PresheafOfModules.tensorObj (O := O₂.obj) F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ)).obj F).val :=
  (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
      (PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val)

/-- **The left arrow of the naturality diagram, before sheafification**: the objectwise tensor
product of the module map `uF` with the canonical map `Ω_{B/A} ⟶ β^*Ω_{B'/A'}`, followed by the
map to the sheafification. -/
noncomputable def differentialsTensorMapPresheaf
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    PresheafOfModules.tensorObj (O := O₂.obj) F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val ⟶
      ((_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O₂').flip.obj
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ')).obj F')).val :=
  PresheafOfModules.tensorHom uF.val (mapDifferentials.{v, u, w, m} φ φ' α β hsq).val ≫
    tensorRestrictScalars (underlyingRingSheafMapOfSite β).hom F'.val
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ').val ≫
    (_root_.PresheafOfModules.restrictScalars
      (underlyingRingSheafMapOfSite β).hom).map
      (tensorSheafifyUnit.{v, u, w, m} φ' F')

/-- **The left arrow of the naturality diagram**: the sheafified tensor product of `uF` with the
canonical map on relative differentials. -/
noncomputable def differentialsTensorMap
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ)).obj F ⟶
      (_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O₂').flip.obj
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ')).obj F') :=
  ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).symm
    (differentialsTensorMapPresheaf.{v, u, w, m} φ φ' α β hsq F F' uF)

/-- **Stacks 09CX.** The change-of-rings maps on first principal parts are compatible with the
inclusions of the short exact sequences of Tag 09CW: the left-hand square of the naturality
diagram commutes, with the tensor product of `uF` and the map on differentials on the left. -/
@[stacks 09CX "sequence naturality: the inclusion square"]
theorem principalPartsSequence_naturality_inclusion
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂') (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂') (hsq : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (F' : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂'))
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj F') :
    (principalPartsInclusion.{v, u, w, m} φ).app F ≫
        principalPartsSquareMap.{v, u, w, m} φ φ' α β hsq F F' uF =
      differentialsTensorMap.{v, u, w, m} φ φ' α β hsq F F' uF ≫
        (_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).map
          ((principalPartsInclusion.{v, u, w, m} φ').app F') := by
  apply ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).injective
  refine Eq.trans ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv_naturality_right _ _)
    (Eq.trans ?_ ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv_naturality_right _ _).symm)
  rw [show ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _)
        (differentialsTensorMap.{v, u, w, m} φ φ' α β hsq F F' uF) =
      differentialsTensorMapPresheaf.{v, u, w, m} φ φ' α β hsq F F' uF from
      Equiv.apply_symm_apply _ _,
    show ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _)
        ((principalPartsInclusion.{v, u, w, m} φ).app F) =
      principalPartsPairingPresheaf.{v, u, w, m} φ F from
      Equiv.apply_symm_apply _ _]
  apply _root_.PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  let _ : Module ((Oforget O₂.obj).obj X) (F.val.obj X) := (F.val.obj X).isModule
  let _ : Module ((Oforget O₂.obj).obj X)
      ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :=
    ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X).isModule
  let _ : Module ((Oforget O₂.obj).obj X)
      (((_root_.SheafOfModules.restrictScalars.{max u v w m}
        (underlyingRingSheafMapOfSite β)).obj
        (principalPartsOne.{v, u, w, m} φ' F')).val.obj X) :=
    (((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj
      (principalPartsOne.{v, u, w, m} φ' F')).val.obj X).isModule
  refine TensorProduct.ext (R := (Oforget O₂.obj).obj X) (M := F.val.obj X)
    (N := (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X)
    (P₂ := ((_root_.SheafOfModules.restrictScalars.{max u v w m}
      (underlyingRingSheafMapOfSite β)).obj
      (principalPartsOne.{v, u, w, m} φ' F')).val.obj X)
    (σ₁₂ := RingHom.id ((Oforget O₂.obj).obj X)) ?_
  refine LinearMap.ext fun x ↦ LinearMap.ext fun ω ↦ ?_
  let _ : Module ((Oforget O₂'.obj).obj X) (F'.val.obj X) := (F'.val.obj X).isModule
  let _ : Module ((Oforget O₂'.obj).obj X)
      ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ').val.obj X) :=
    ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ').val.obj X).isModule
  refine Eq.trans ?_ (principalPartsInclusion_toSheafify.{v, u, w, m} φ' F' X
    (TensorProduct.mk ((ringPresheaf O₂'.obj).obj X)
      (F'.val.obj X) ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' φ').val.obj X)
      ((uF.val.app X).hom x)
      (((mapDifferentials.{v, u, w, m} φ φ' α β hsq).val.app X).hom ω))).symm
  exact congrArg
    (fun k : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
        internalHomSheafOfModules F ((_root_.SheafOfModules.restrictScalars.{max u v w m}
          (underlyingRingSheafMapOfSite β)).obj
          (principalPartsOne.{v, u, w, m} φ' F')) ↦
      (((k.val.app X).hom ω).app (op (Over.mk (𝟙 X.unop)))).hom x)
    (principalPartsInclusionHom_square.{v, u, w, m} φ φ' α β hsq F F' uF)

end Inclusion

end AlgebraicGeometry.SheafOfModules

end
