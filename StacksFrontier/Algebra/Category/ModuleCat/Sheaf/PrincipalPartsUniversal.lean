module

public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators
import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials and principal parts as universal objects

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site. The functor
sending a sheaf of `O₂`-modules to the type of its relative derivations is corepresentable
(Tag 04BL), and for a fixed sheaf of modules `F` and an integer `k` the functor sending a
sheaf of `O₂`-modules to the type of differential operators of order at most `k` out of `F`
is corepresentable (Tag 09CT). Both facts are available on this branch only as the
propositions `IsCorepresentable`; this file turns them into the interface their consumers
actually use: a named representing object, a named universal element, and the
unique-factorization property of that universal element.

It then builds the first thing that property gives: the module of principal parts of order
at most `k` is functorial in the coefficient module, and the universal operator of order `0`
exhibits a natural transformation from that functor to the identity functor, which is the
surjection `Pᵏ ⟶ P⁰ = F` of the discussion following Tag 09CU.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite`: the sheaf of relative
  differentials `Ω_{O₂/O₁}`, with `universalDerivationOfSite` its universal derivation.
* `AlgebraicGeometry.SheafOfModules.moduleOfPrincipalParts`: the sheaf of principal parts
  `Pᵏ_{O₂/O₁}(F)`, with `universalDiffOp` its universal differential operator.
* `AlgebraicGeometry.SheafOfModules.principalPartsMap` and
  `AlgebraicGeometry.SheafOfModules.principalPartsFunctor`: the functoriality of principal
  parts in the coefficient module.
* `AlgebraicGeometry.SheafOfModules.principalPartsProjection`: the natural transformation
  `Pᵏ_{O₂/O₁}(-) ⟶ 𝟭`.

## Main results

* `AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation`: every relative derivation
  with values in a sheaf of modules factors through the universal derivation by a unique
  morphism of sheaves of modules. This is Tag 04BL in unique-factorization form.
* `AlgebraicGeometry.SheafOfModules.existsUnique_descDiffOp`: the same for differential
  operators of order at most `k`, which is Tag 09CT in unique-factorization form.
* `AlgebraicGeometry.SheafOfModules.principalPartsMap_universalDiffOp` and
  `AlgebraicGeometry.SheafOfModules.principalPartsProjection_universalDiffOp`: the two maps
  are pinned by their effect on the universal operator, `D_F x ↦ D_G (f x)` and `D_F x ↦ x`.

## Implementation notes

The representing objects are `Functor.coreprX` of the two functors and the universal
elements are `Functor.coreprx`, so nothing here chooses a construction: everything is
derived from the corepresentability propositions
`derivationsFunctor_isCorepresentable` and
`differentialOperatorsFunctor_isCorepresentable` proved elsewhere on this branch. The
unique-factorization statements are `Functor.CorepresentableBy.homEquiv` together with
`Functor.CorepresentableBy.homEquiv_eq`, which identifies the bijection with
postcomposition of the universal element; for differential operators the bijection lands in
a subtype, so the factorization equation is extracted with `Subtype.ext`.

Universes. The site is `C : Type u` with `Category.{v} C` and the structure sheaves are
`CommRingCat.{w}`-valued, resp. `RingCat.{w}`-valued; coefficient sheaves of modules live in
`SheafOfModules.{max u v w m}` for a free universe parameter `m`. This is the universe in
which both corepresentability statements are available and is forced rather than chosen: the
hom types of `SheafOfModules.{t}` on this site live in `Type (max u v t)`, so a functor to
`Type t` can only be corepresentable when `t` absorbs `max u v`, and the representing objects
are built from the structure sheaves, so `t` must absorb `w` as well. Nothing is narrowed:
`u`, `v`, `w`, `m` are free and the site is an arbitrary category, not assumed small.

Functoriality of principal parts is *forced*, not constructed: for `f : F ⟶ G` the composite
of the universal operator of `G` with `f` is an operator of order at most `k` out of `F`
(composition of an order-`0` and an order-`k` operator), so it factors uniquely through the
universal operator of `F`, and the functor laws are instances of that uniqueness. The
projection is the factorization of the identity, which is an operator of order `0` and hence
of order at most `k`.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), and
  [Tag 09CU](https://stacks.math.columbia.edu/tag/09CU), the module of principal parts.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m

namespace DiffOp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J RingCat.{w}} (phi : O₁ ⟶ O₂)
  {F G : _root_.SheafOfModules.{m} O₂} {D : DiffOp.GlobalOp F G}

/-- A differential operator of order at most `k` is one of order at most `k + 1`. -/
theorem isGlobalDiffOpOfOrder_succ {k : ℕ}
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D) :
    DiffOp.IsGlobalDiffOpOfOrder phi (k + 1) D := fun U ↦
  RawOp.isDiffOpOfOrder_succ_of_isDiffOpOfOrder phi k _ (hD U)

/-- A differential operator of order at most `k` is one of order at most `k + l`. -/
theorem isGlobalDiffOpOfOrder_add_right {k : ℕ} (l : ℕ)
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D) :
    DiffOp.IsGlobalDiffOpOfOrder phi (k + l) D := by
  induction l with
  | zero => exact hD
  | succ l ih => exact isGlobalDiffOpOfOrder_succ phi ih

end DiffOp

namespace AlgebraicGeometry.SheafOfModules

section Derivations

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O₁ O₂ : Sheaf J CommRingCat.{w}) (φ : O₁ ⟶ O₂)

/-- The sheaf of relative differentials `Ω_{O₂/O₁}`: the sheaf of modules corepresenting the
functor of relative derivations. -/
@[stacks 04BN "the module of differentials `Ω_{O₂/O₁}`"]
noncomputable abbrev moduleOfDifferentialsOfSite :
    _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  (derivationsFunctor.{m} O₁ O₂ φ).coreprX

/-- The universal relative derivation with values in `Ω_{O₂/O₁}`. -/
@[stacks 04BN "the module of differentials `Ω_{O₂/O₁}`",
  ega "IV 16.3.6" "dt",
  ega "IV 16.5.3" "(i)"]
noncomputable def universalDerivationOfSite :
    PresheafOfModulesOfCommRing.Derivation' (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val
      φ.hom :=
  (derivationsFunctor.{m} O₁ O₂ φ).coreprx

/-- **Stacks 04BL**, in unique-factorization form: every relative derivation with values in a
sheaf of modules factors through the universal derivation by a unique morphism of sheaves of
modules. -/
@[stacks 04BL "unique-factorization form, on an arbitrary site"]
theorem existsUnique_descDerivation
    (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val φ.hom) :
    ∃! f : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶ F,
      (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp f.val = D := by
  set e := (derivationsFunctor.{m} O₁ O₂ φ).corepresentableBy
  obtain ⟨f, hf, hu⟩ := e.homEquiv.bijective.existsUnique D
  exact ⟨f, (e.homEquiv_eq f).symm.trans hf, fun g hg ↦ hu g ((e.homEquiv_eq g).trans hg)⟩

end Derivations

section PrincipalParts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J RingCat.{w}} (phi : O₁ ⟶ O₂)

/-- A morphism of sheaves of modules is a differential operator of order at most `k`. -/
theorem homGlobalOp_isGlobalDiffOpOfOrder (k : ℕ)
    {F G : _root_.SheafOfModules.{m} O₂} (f : F ⟶ G) :
    DiffOp.IsGlobalDiffOpOfOrder phi k (homGlobalOp f) := by
  simpa using
    DiffOp.isGlobalDiffOpOfOrder_add_right phi k (homGlobalOp_isOrderZero phi f)

/-- The sheaf of principal parts `Pᵏ_{O₂/O₁}(F)`: the sheaf of modules corepresenting the
functor of differential operators of order at most `k` out of `F`. -/
@[stacks 09CU "the module of principal parts of order k", sga "6 II AppII.1.2.2" "P^n_{X/S}(E)"]
noncomputable abbrev moduleOfPrincipalParts
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    _root_.SheafOfModules.{max u v w m} O₂ :=
  (differentialOperatorsFunctor.{v, u, w, m} phi F k).coreprX

/-- The universal differential operator of order at most `k` out of `F`. -/
noncomputable def universalDiffOp (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    DiffOp.GlobalOp F (moduleOfPrincipalParts.{v, u, w, m} phi F k) :=
  (differentialOperatorsFunctor.{v, u, w, m} phi F k).coreprx.1

/-- The universal differential operator has order at most `k`. -/
theorem universalDiffOp_isGlobalDiffOpOfOrder
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    DiffOp.IsGlobalDiffOpOfOrder phi k (universalDiffOp.{v, u, w, m} phi F k) :=
  (differentialOperatorsFunctor.{v, u, w, m} phi F k).coreprx.2

/-- **Stacks 09CT**, in unique-factorization form: every differential operator of order at
most `k` out of `F` factors through the universal one by a unique morphism of sheaves of
modules. -/
@[stacks 09CT "unique-factorization form",
  ega "IV 16.8.3" "(16.8.3.1)",
  sga "6 II AppII.1.2.3",
  sga "6 II AppII.1.2.2" "(1.2.2.1)"]
theorem existsUnique_descDiffOp
    (F G : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ)
    (D : DiffOp.GlobalOp F G) (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D) :
    ∃! f : moduleOfPrincipalParts.{v, u, w, m} phi F k ⟶ G,
      postcomp (universalDiffOp.{v, u, w, m} phi F k) f = D := by
  set e := (differentialOperatorsFunctor.{v, u, w, m} phi F k).corepresentableBy
  obtain ⟨f, hf, hu⟩ := e.homEquiv.bijective.existsUnique ⟨D, hD⟩
  exact ⟨f, (congrArg Subtype.val (e.homEquiv_eq f)).symm.trans (congrArg Subtype.val hf),
    fun g hg ↦ hu g (Subtype.ext ((congrArg Subtype.val (e.homEquiv_eq g)).trans hg))⟩

/-- The composite of the universal operator of `G` with a morphism `f : F ⟶ G` is a
differential operator of order at most `k` out of `F`. -/
theorem comp_homGlobalOp_isGlobalDiffOpOfOrder
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) (k : ℕ) :
    DiffOp.IsGlobalDiffOpOfOrder phi k
      ((universalDiffOp.{v, u, w, m} phi G k).comp (homGlobalOp f)) := by
  simpa using DiffOp.isGlobalDiffOpOfOrder_comp phi (homGlobalOp f)
    (universalDiffOp.{v, u, w, m} phi G k) (homGlobalOp_isOrderZero phi f)
    (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m} phi G k)

/-- The morphism of sheaves of principal parts induced by a morphism `f : F ⟶ G` of
coefficient modules: the factorization of `D_G ∘ f` through `D_F`. -/
noncomputable def principalPartsMap
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) (k : ℕ) :
    moduleOfPrincipalParts.{v, u, w, m} phi F k ⟶
      moduleOfPrincipalParts.{v, u, w, m} phi G k :=
  (existsUnique_descDiffOp.{v, u, w, m} phi F _ k _
    (comp_homGlobalOp_isGlobalDiffOpOfOrder.{v, u, w, m} phi f k)).choose

/-- The characterizing property of `principalPartsMap`. -/
theorem postcomp_principalPartsMap
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) (k : ℕ) :
    postcomp (universalDiffOp.{v, u, w, m} phi F k)
        (principalPartsMap.{v, u, w, m} phi f k)
      = (universalDiffOp.{v, u, w, m} phi G k).comp (homGlobalOp f) :=
  (existsUnique_descDiffOp.{v, u, w, m} phi F _ k _
    (comp_homGlobalOp_isGlobalDiffOpOfOrder.{v, u, w, m} phi f k)).choose_spec.1

/-- A morphism of sheaves of principal parts carrying `D_F` to `D_G ∘ f` is
`principalPartsMap`. -/
theorem principalPartsMap_unique
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) (k : ℕ)
    (β : moduleOfPrincipalParts.{v, u, w, m} phi F k ⟶
      moduleOfPrincipalParts.{v, u, w, m} phi G k)
    (hβ : postcomp (universalDiffOp.{v, u, w, m} phi F k) β
      = (universalDiffOp.{v, u, w, m} phi G k).comp (homGlobalOp f)) :
    β = principalPartsMap.{v, u, w, m} phi f k :=
  (existsUnique_descDiffOp.{v, u, w, m} phi F _ k _
    (comp_homGlobalOp_isGlobalDiffOpOfOrder.{v, u, w, m} phi f k)).choose_spec.2 β hβ

/-- `principalPartsMap` on local sections: it carries the universal operator applied to `x`
to the universal operator applied to `f x`. -/
theorem principalPartsMap_universalDiffOp
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) (k : ℕ)
    (X : Cᵒᵖ) (x : F.val.obj X) :
    ((principalPartsMap.{v, u, w, m} phi f k).val.app X).hom
        (universalDiffOp.{v, u, w, m} phi F k X x)
      = universalDiffOp.{v, u, w, m} phi G k X ((f.val.app X).hom x) :=
  congrArg (fun D : DiffOp.GlobalOp F _ ↦ D X x)
    (postcomp_principalPartsMap.{v, u, w, m} phi f k)

/-- The functor of principal parts of order at most `k`, in the coefficient module. -/
noncomputable def principalPartsFunctor (k : ℕ) :
    _root_.SheafOfModules.{max u v w m} O₂ ⥤ _root_.SheafOfModules.{max u v w m} O₂ where
  obj F := moduleOfPrincipalParts.{v, u, w, m} phi F k
  map f := principalPartsMap.{v, u, w, m} phi f k
  map_id F := (principalPartsMap_unique.{v, u, w, m} phi (𝟙 F) k (𝟙 _) rfl).symm
  map_comp {F G H} f g :=
    (principalPartsMap_unique.{v, u, w, m} phi (f ≫ g) k
      (principalPartsMap.{v, u, w, m} phi f k ≫
        principalPartsMap.{v, u, w, m} phi g k)
      (by
        funext X
        refine AddMonoidHom.ext fun x ↦ ?_
        change ((principalPartsMap.{v, u, w, m} phi g k).val.app X).hom
            (((principalPartsMap.{v, u, w, m} phi f k).val.app X).hom
              (universalDiffOp.{v, u, w, m} phi F k X x)) = _
        rw [principalPartsMap_universalDiffOp.{v, u, w, m} phi f k X x,
          principalPartsMap_universalDiffOp.{v, u, w, m} phi g k X _]
        rfl)).symm

/-- `principalPartsFunctor` sends `F` to its module of principal parts of order at most `k`. -/
@[simp]
theorem principalPartsFunctor_obj (k : ℕ)
    (F : _root_.SheafOfModules.{max u v w m} O₂) :
    (principalPartsFunctor.{v, u, w, m} phi k).obj F
      = moduleOfPrincipalParts.{v, u, w, m} phi F k := rfl

/-- `principalPartsFunctor` sends a morphism `f` to the induced map `principalPartsMap phi f k`. -/
@[simp]
theorem principalPartsFunctor_map (k : ℕ)
    {F G : _root_.SheafOfModules.{max u v w m} O₂} (f : F ⟶ G) :
    (principalPartsFunctor.{v, u, w, m} phi k).map f
      = principalPartsMap.{v, u, w, m} phi f k := rfl

/-- The retraction `Pᵏ_{O₂/O₁}(F) ⟶ F` of the universal operator: the factorization of the
identity of `F`, which is a differential operator of order `0`. -/
noncomputable def principalPartsRetraction
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    moduleOfPrincipalParts.{v, u, w, m} phi F k ⟶ F :=
  (existsUnique_descDiffOp.{v, u, w, m} phi F F k (homGlobalOp (𝟙 F))
    (homGlobalOp_isGlobalDiffOpOfOrder phi k (𝟙 F))).choose

/-- `principalPartsRetraction` on local sections: it retracts the universal operator. -/
theorem principalPartsRetraction_universalDiffOp
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) (X : Cᵒᵖ) (x : F.val.obj X) :
    ((principalPartsRetraction.{v, u, w, m} phi F k).val.app X).hom
        (universalDiffOp.{v, u, w, m} phi F k X x) = x :=
  congrArg (fun D : DiffOp.GlobalOp F F ↦ D X x)
    (existsUnique_descDiffOp.{v, u, w, m} phi F F k (homGlobalOp (𝟙 F))
      (homGlobalOp_isGlobalDiffOpOfOrder phi k (𝟙 F))).choose_spec.1

/-- The natural transformation `Pᵏ_{O₂/O₁}(-) ⟶ 𝟭` retracting the universal operator: the
surjection `Pᵏ ⟶ P⁰ = F` of the discussion following Tag 09CU. -/
noncomputable def principalPartsProjection (k : ℕ) :
    principalPartsFunctor.{v, u, w, m} phi k ⟶
      𝟭 (_root_.SheafOfModules.{max u v w m} O₂) where
  app F := principalPartsRetraction.{v, u, w, m} phi F k
  naturality {F G} f :=
    (existsUnique_descDiffOp.{v, u, w, m} phi F G k
      ((homGlobalOp f).comp (homGlobalOp (𝟙 F)))
      (by
        simpa using DiffOp.isGlobalDiffOpOfOrder_comp phi (homGlobalOp (𝟙 F))
          (homGlobalOp f) (homGlobalOp_isGlobalDiffOpOfOrder phi k (𝟙 F))
          (homGlobalOp_isOrderZero phi f))).unique
      (by
        funext X
        exact AddMonoidHom.ext fun x ↦ (congrArg
          (fun y ↦ ((principalPartsRetraction.{v, u, w, m} phi G k).val.app X).hom y)
            (principalPartsMap_universalDiffOp.{v, u, w, m} phi f k X x)).trans
          (principalPartsRetraction_universalDiffOp.{v, u, w, m} phi G k X _))
      (by
        funext X
        exact AddMonoidHom.ext fun x ↦ congrArg (fun y ↦ ((f.val.app X).hom) y)
          (principalPartsRetraction_universalDiffOp.{v, u, w, m} phi F k X x))

/-- `principalPartsProjection` on local sections: it retracts the universal operator. -/
theorem principalPartsProjection_universalDiffOp (k : ℕ)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (X : Cᵒᵖ) (x : F.val.obj X) :
    (((principalPartsProjection.{v, u, w, m} phi k).app F).val.app X).hom
        (universalDiffOp.{v, u, w, m} phi F k X x) = x :=
  principalPartsRetraction_universalDiffOp.{v, u, w, m} phi F k X x

end PrincipalParts

end AlgebraicGeometry.SheafOfModules

end
