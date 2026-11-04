module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquare
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCanonical

/-!
# The canonical projection morphism is the change-of-rings isomorphism transposed

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit` builds the *canonical
projection morphism* `Dualizing.ProjectionFormula.canonicalProjInv`

`ω_{G,N} : i_*G ⊗ᴸ_A N ⟶ i_*(G ⊗ᴸ_B Ext N)`

out of the unit and the counit of [stacks 0GMT] and the section `ν` of the lax monoidal structure
map `μ` of derived base change, and
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCanonical` reduces the second input
of [stacks 0E2H] to a coherence of `ν` written with `ω`.

This file removes `ν` and `μ` from `ω` altogether, and removes both adjunctions from that
coherence.  The only input is the transposition formula
`Dualizing.homEquiv_derivedTensorBaseChangeSection`, which says that precomposition with `ν` is the
composite of the four adjunction bijections, together with the two triangle identities.

## Main results

* `Dualizing.derivedTensorBaseChangeSection_naturality` — `ν` is natural in both variables.  It is
  the inverse of `Dualizing.derivedTensorBaseChange`, which is natural by
  `Dualizing.derivedTensorBaseChange_naturality`.
* `Dualizing.ProjectionFormula.canonicalProjInv_eq` — **the canonical projection morphism with no
  `ν` in it.**  `ω_{G,N}` is the transpose over the tensor--Hom adjunction of [stacks 0A63] of

  `i_*G --i_*(coev)--> i_*RHom_B(Ext N, G ⊗ᴸ_B Ext N) --0E1W--> RHom_A(N, i_*(G ⊗ᴸ_B Ext N))`,

  built from derived restriction of the coevaluation of [stacks 0A63] over `B` and the
  change-of-rings isomorphism of [stacks 0E1W] alone.  Neither `μ` nor `ν` nor the unit of
  [stacks 0GMT] occurs: the unit is absorbed by a triangle identity.
* `Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation` — **the change-of-rings
  isomorphism of [stacks 0E1W] is compatible with evaluation**, unconditionally: the component of
  [stacks 0E1W] at `(N, W)`, tensored with `N` and evaluated over `A`, is the canonical projection
  morphism at `(RHom_B(Ext N, W), N)` followed by derived restriction of evaluation over `B`.  This
  is the compatibility the second identification of [stacks 0E2H] asks for, and it is a corollary
  of the previous result and the triangle identity of the tensor--Hom adjunction.
* `Dualizing.ProjectionFormula.tensor_map_comp_canonicalProjInv` — **`ω` after an arbitrary
  morphism into a restriction**: for `g : X ⟶ i_*G` the composite `(g ⊗ᴸ 𝟙_Y) ≫ ω_{G,Y}` is the
  transpose over [stacks 0GMT] of `ν_{X,Y}` followed by the transpose of `g` tensored with
  `𝟙_{Ext Y}`.  Both the unit and the counit of [stacks 0GMT] are gone from the right-hand side.
* `Dualizing.ProjectionFormula.unit_tensor_comp_canonicalProjInv` — **`ν` is the canonical
  projection morphism restricted along the unit**: at `G = Ext M` and `N = Y`, precomposing
  `ω_{Ext M, Y}` with `η_M ⊗ᴸ 𝟙_Y` gives `η_{M ⊗ᴸ_A Y}` followed by derived restriction of
  `ν_{M,Y}`.
* `Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence` — **the residue of
  [stacks 0E2H] with no adjunction in it**: the equation

  `Ext(c_{M ⊗ᴸ Y}) ≫ ε ≫ ν_{M,Y} = Ext(r) ≫ ν_{M ⊗ᴸ T, Y} ≫ ((Ext(c_M) ≫ ε) ⊗ᴸ 𝟙_{Ext Y})`

  of morphisms `Ext((M ⊗ᴸ_A Y) ⊗ᴸ_A T) ⟶ Ext M ⊗ᴸ_B Ext Y` in `D(B)`, with `c` for
  `Dualizing.ProjectionFormula.canonicalRestrictExtendInv`, `T = i_*(1_B)` for the algebra, `ε`
  for the counit of [stacks 0GMT] and `r` for the symmetry-and-associativity rearrangement of
  [stacks 0A63].  No unit, no derived restriction of scalars, no transposition and no internal
  Hom occurs.
* `Dualizing.ProjectionFormula.canonicalProjTensorBaseChangeCompat_iff_coherence` — **the
  reduction**: `Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` holds exactly
  when that coherence does.  Unconditional.

## What this says about the residue of [stacks 0E2H]

The second input of [stacks 0E2H] is
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat`, an equation between two
morphisms `(M ⊗ᴸ_A Y) ⊗ᴸ_A i_*(1_B) ⟶ i_*(Ext M ⊗ᴸ_B Ext Y)` built from `ω`, `ν` and the symmetric
monoidal structure of [stacks 0A63].  Both of its sides are transposes over [stacks 0GMT] -- the
left one because it is a morphism into a restriction followed by the restriction of `ν`, the right
one by `Dualizing.ProjectionFormula.tensor_map_comp_canonicalProjInv` -- so the whole of it
transposes to a single equation in `D(B)`,
`Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence`.  That is as far as the
adjunctions go.  What is left is not reducible by them: expanding `c` through
`Dualizing.ProjectionFormula.canonicalProjInv_eq` and reading both sides through the transposition
formula `Dualizing.homEquiv_derivedTensorBaseChangeSection` produces the component of
[stacks 0E1W] at the pair `(M ⊗ᴸ_A Y, -)` on one side and at `(Y, -)` on the other, and relating
the two is the compatibility of [stacks 0E1W] with the *currying* isomorphism of [stacks 0A65].
That compatibility is equivalent to the associativity of `μ`, and neither is proved here or
anywhere in this library.

That equivalence is a theorem.  `Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.CurryingCoherence` proves that the pentagon
`Dualizing.DerivedTensorBaseChangeAssoc` of `μ` and the compatibility
`Dualizing.DerivedHomBaseChangeCurryCompat` of the morphism of [stacks 0E1X] --- hence of
[stacks 0E1W], the two differing by derived Hom of the unit of [stacks 0GMT] --- with the currying
isomorphism of [stacks 0A65] are the same statement, each being the other at a single object.  It
is proved abstractly, for an arbitrary adjunction and an arbitrary comparison of internal-Hom
bifunctors, as
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_homMateCurryCompat`: the pentagon
of a lax tensor comparison obtained as a mate *is* the closed-functor axiom of Eilenberg--Kelly for
that mate.  The currying isomorphism itself is `Dualizing.homCurryIso`, whose characterizing law is
`Dualizing.homEquiv_homEquiv_comp_homCurryIso_hom`.

So the residue of the second input of [stacks 0E2H] is one coherence, now in a shape with no
adjunction in it, and equally expressible as the associativity of `μ`, as the associativity of
`ω`, or as the compatibility of [stacks 0E1W] with currying.  Its *evaluation* half is free:
`Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation`.

Two further remarks.  First, the determinate chain-level route exists.
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_monoidalIso` values the
morphism of [stacks 0E1X] with no existential and with the degreewise monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` as its only chain map, and
`Dualizing.derivedTensorBaseChange_eq_evaluation` carries that value to `μ`, so the chain map
produced existentially by `Dualizing.derivedTensorBaseChange_eq_model` is not needed.  What is
still missing is not a value but a coherence *of* that value, in the three links the module
documentation of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.CurryingCoherence` names.  The first of
those three is **proved**: the chain-level pentagon of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` is
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`, unconditional and for
arbitrary cochain complexes, resting on the triple-summand reading
`CochainComplex.ExtendScalars.ιTensorObj_associator_hom` of the associator of total tensor
products.  The two that remain are the identification of `μ` at a K-flat pair with
`CochainComplex.ExtendScalars.derivedMonoidalIso` and the transport of the pentagon along
isomorphisms of its three arguments; both are transport, neither is stated here.  `ν` inherits
the value through the same
conjugation, being a transpose of a component of [stacks 0E1W], but no declaration states it.  The
[stacks 068I] morphism `Dualizing.tensorBaseChangeMor` does have a chain-level value at K-flat
pairs, `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, but its identification with `μ` exists only
as the `Iff` `Dualizing.tensorBaseChangeMor_eq_iff`, as
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` — which is that `Iff` with the component of
[stacks 0E1W] read through its inverse, the direction whose model value
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` inverts
nothing — and as the hypothesis of
`Dualizing.tensorBaseChangeMor_eq_of_kFlat`.  Second, `baseChange_tensor_iso` is not a chain-level
model of `μ`: it is the chain-level *projection formula*
`(L ⊗ᴸ_{R'} (R' ⊗ᴸ_R K))|_R ≅ L|_R ⊗ᴸ_R K`, and it occurs in this library only as a factor of
`Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`, i.e. as an input to
`Dualizing.ProjectionFormula.ProjCounitCompat` and not to the coherence of `μ`.

No `@[stacks]` attribute is placed here: the results below are identities between named morphisms
and belong to the tags of the morphisms they are about.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

universe ur uv uw

/-- **The transpose of a morphism tensored with the identity.**  For `e : X ⟶ X'` the morphism
`e ⊗ᴸ 𝟙_Y` is the transpose over the tensor--Hom adjunction of [stacks 0A63] of `e` followed by
the coevaluation `X' ⟶ RHom(Y, X' ⊗ᴸ Y)`. -/
theorem homEquiv_symm_tensor_map_id {R : Type ur} [CommRing R]
    [HasDerivedCategory.{uw} (ModuleCat.{uv} R)] (d : DerivedHomAdjunction R)
    (X X' Y : DerivedCategory (ModuleCat.{uv} R)) (e : X ⟶ X') :
    (d.homEquiv X Y (d.tensor.obj (X', Y))).symm
        (d.tensor.map ((e, 𝟙 Y) : (X, Y) ⟶ (X', Y))) =
      e ≫ d.tensorHomUnit X' Y := by
  have h : d.homEquiv X Y (d.tensor.obj (X', Y)) (e ≫ d.tensorHomUnit X' Y) =
      d.tensor.map ((e, 𝟙 Y) : (X, Y) ⟶ (X', Y)) := by
    rw [d.homEquiv_naturality_left,
      show d.homEquiv X' Y (d.tensor.obj (X', Y)) (d.tensorHomUnit X' Y) = 𝟙 _ from
        (d.homEquiv X' Y (d.tensor.obj (X', Y))).apply_symm_apply (𝟙 _),
      Category.comp_id]
  rw [← h, AddEquiv.symm_apply_apply]

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

section SectionNaturality

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The section of the lax monoidal structure map of derived base change is natural in both
variables.**  `Dualizing.derivedTensorBaseChange` is natural by
`Dualizing.derivedTensorBaseChange_naturality` and `Dualizing.derivedTensorBaseChangeSection` is a
two-sided inverse of it, by
`Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange` and
`Dualizing.derivedTensorBaseChange_comp_derivedTensorBaseChangeSection`. -/
theorem derivedTensorBaseChangeSection_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{max uR uA uM} R)} (x : X ⟶ X') (y : Y ⟶ Y') :
    F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          ((x, y) : (X, Y) ⟶ (X', Y'))) ≫
        derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X' Y' =
      derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
          ((F.map x, F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) := by
  calc _ = (derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
            derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y) ≫
          F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.map ((x, y) : (X, Y) ⟶ (X', Y'))) ≫
            derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X' Y' := by
        rw [derivedTensorBaseChangeSection_comp_derivedTensorBaseChange.{uR, uA, uM} f F
          comparison X Y, Category.id_comp]
    _ = derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
                ((F.map x, F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) ≫
              derivedTensorBaseChange.{uR, uA, uM} f F comparison X' Y') ≫
            derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X' Y' := by
        simp only [Category.assoc,
          reassoc_of% derivedTensorBaseChange_naturality.{uR, uA, uM} f F comparison x y]
    _ = derivedTensorBaseChangeSection.{uR, uA, uM} f F comparison X Y ≫
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
            ((F.map x, F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) := by
        rw [Category.assoc, derivedTensorBaseChange_comp_derivedTensorBaseChangeSection.{uR, uA, uM}
          f F comparison X' Y', Category.comp_id]

end SectionNaturality

namespace ProjectionFormula

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

/-! ### The canonical projection morphism with no structure map in it -/

/-- The transpose of a morphism followed by the restriction of a morphism: the counit of the
adjunction absorbs the unit by a triangle identity. -/
private theorem homEquiv_counit_comp {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rf : D ⥤ C} (adj : L ⊣ Rf) {Z W : D} (k : Z ⟶ W) :
    adj.homEquiv (Rf.obj Z) W (adj.counit.app Z ≫ k) = Rf.map k := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]

/-- **The canonical projection morphism is the change-of-rings isomorphism of [stacks 0E1W]
transposed.**  Writing `i_*` for derived restriction of scalars, `Ext` for the model `E` and `coev`
for the coevaluation of [stacks 0A63] over `B`, the morphism
`Dualizing.ProjectionFormula.canonicalProjInv` at `(N, G)` is the transpose over the tensor--Hom
adjunction of [stacks 0A63] over `A` of

`i_*G --i_*(coev)--> i_*RHom_B(Ext N, G ⊗ᴸ_B Ext N) --0E1W--> RHom_A(N, i_*(G ⊗ᴸ_B Ext N))`.

Neither the lax monoidal structure map `μ` of derived base change nor its section `ν` occurs, and
neither does the unit of [stacks 0GMT]: the transposition formula
`Dualizing.homEquiv_derivedTensorBaseChangeSection` replaces `ν` by the component of
[stacks 0E1W], the counit of [stacks 0GMT] is absorbed into coevaluation by
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_tensor_map_id`, and the unit is then
absorbed by a triangle identity. -/
theorem canonicalProjInv_eq (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    canonicalProjInv.{u, v} φ E N G =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
              (G, E.functor.obj N)))
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensorHomUnit G
              (E.functor.obj N)) ≫
          homRestrictComponent.{u, v} φ E N
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
              (G, E.functor.obj N))) := by
  have hg := DerivedHomAdjunction.homEquiv_symm_tensor_map_id
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B)
    (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G)) G
    (E.functor.obj N) ((modelAdjunction.{u, v} φ E).counit.app G)
  have hstar := homEquiv_derivedTensorBaseChangeSection.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E)
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N
    ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj (G, E.functor.obj N))
    (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv
          (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G))
          (E.functor.obj N)
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
            (G, E.functor.obj N))).symm
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
        (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
          E.functor.obj N))
        (Y := (G, E.functor.obj N))
        ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj N))))
  rw [AddEquiv.apply_symm_apply, hg, homEquiv_counit_comp] at hstar
  dsimp only [canonicalProjInv, homRestrictComponent]
  rw [← Adjunction.homEquiv_unit]
  exact hstar.symm

/-! ### [stacks 0E1W] is compatible with evaluation -/

/-- The naturality of the change-of-rings isomorphism of [stacks 0E1W] in its covariant variable,
read with the internal Hom of the tensor--Hom adjunction of [stacks 0A63] rather than with the
transported bifunctor `Stacks.DerivedHom.ScalarTransportedInternalHom.hom` its own statement uses.
The two are definitionally equal but not syntactically so, which is why the naturality square is
restated by `exact` rather than used directly. -/
private theorem homRestrictComponent_naturality_right (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    {W W' : DerivedCategory (ModuleCat.{max u v} B)} (k : W ⟶ W') :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.map
            ((𝟙 (Opposite.op (E.functor.obj N)), k) :
              (Opposite.op (E.functor.obj N), W) ⟶ (Opposite.op (E.functor.obj N), W'))) ≫
        homRestrictComponent.{u, v} φ E N W' =
      homRestrictComponent.{u, v} φ E N W ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.map
          ((𝟙 (Opposite.op N),
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map k) :
            (Opposite.op N,
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W) ⟶
              (Opposite.op N,
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W')) := by
  have hnat := (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, v} φ
    E.functor (modelComparison.{u, v} φ E)).inv.naturality
    ((𝟙 (Opposite.op N), k) :
      ((Opposite.op N, W) :
          (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ×
            DerivedCategory (ModuleCat.{max u v} B)) ⟶ (Opposite.op N, W'))
  simp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map, unop_id,
    CategoryTheory.Functor.map_id, op_id] at hnat
  exact hnat

/-- **The change-of-rings isomorphism of [stacks 0E1W] is compatible with evaluation.**  Writing
`i_*` for derived restriction of scalars and `Ext` for the model `E`, the component of
[stacks 0E1W] at `(N, W)` tensored with `N` and evaluated over `A` is the canonical projection
morphism at `(RHom_B(Ext N, W), N)` followed by `i_*` of evaluation over `B`:

`i_*RHom_B(Ext N, W) ⊗ᴸ_A N --ω--> i_*(RHom_B(Ext N, W) ⊗ᴸ_B Ext N) --i_*(ev_B)--> i_*W`

is `(0E1W ⊗ᴸ 𝟙_N) ≫ ev_A`.  Unconditional: no coherence is assumed.  It is
`Dualizing.ProjectionFormula.canonicalProjInv_eq` together with the triangle identity
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_map_evaluation` of the tensor--Hom
adjunction of [stacks 0A63] over `B`, which cancels the coevaluation that
`Dualizing.ProjectionFormula.canonicalProjInv_eq` leaves. -/
theorem canonicalProjInv_comp_restrict_evaluation (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    canonicalProjInv.{u, v} φ E N
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W)) ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
            (E.functor.obj N) W) =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                (Opposite.op (E.functor.obj N), W)), N))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.obj
              (Opposite.op N,
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W), N))
          (homRestrictComponent.{u, v} φ E N W, 𝟙 N) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).evaluation N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W) := by
  have hcancel :
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensorHomUnit
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                (Opposite.op (E.functor.obj N), W)) (E.functor.obj N)) ≫
          homRestrictComponent.{u, v} φ E N
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
                ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                  (Opposite.op (E.functor.obj N), W), E.functor.obj N)) ≫
            (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.map
              ((𝟙 (Opposite.op N),
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                    ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
                      (E.functor.obj N) W)) :
                (Opposite.op N,
                    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                      ((derivedHomAdjunctionOverRing.{u, max u v,
                        max u v + 1} B).tensor.obj
                        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                          (Opposite.op (E.functor.obj N), W), E.functor.obj N))) ⟶
                  (Opposite.op N,
                    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)) =
        homRestrictComponent.{u, v} φ E N W := by
    rw [← homRestrictComponent_naturality_right.{u, v} φ E N
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
          (E.functor.obj N) W),
      ← Category.assoc, ← Functor.map_comp,
      DerivedHomAdjunction.tensorHomUnit_comp_map_evaluation, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [canonicalProjInv_eq.{u, v} φ E N
    ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W))]
  refine Eq.trans ?_ (DerivedHomAdjunction.homEquiv_eq_tensor_map_comp_evaluation
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A)
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
        (Opposite.op (E.functor.obj N), W))) N
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
    (homRestrictComponent.{u, v} φ E N W))
  rw [← (Category.assoc _ _ _).trans hcancel]
  exact ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv_naturality_right
    _ _).symm

/-! ### The canonical projection morphism after an arbitrary morphism into a restriction -/

/-- A morphism into a restriction followed by the restriction of a morphism, as a transpose. -/
private theorem comp_map_eq_homEquiv {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rf : D ⥤ C} (adj : L ⊣ Rf) {X : C} {Z W : D} (g : X ⟶ Rf.obj Z) (k : Z ⟶ W) :
    g ≫ Rf.map k = adj.homEquiv X W (L.map g ≫ adj.counit.app Z ≫ k) := by
  rw [Adjunction.homEquiv_naturality_left, homEquiv_counit_comp]

/-- **The canonical projection morphism after an arbitrary morphism into a restriction.**  For
`g : X ⟶ i_*G` the composite `(g ⊗ᴸ 𝟙_Y) ≫ ω_{G,Y}` is the transpose over [stacks 0GMT] of

`Ext(X ⊗ᴸ_A Y) --ν_{X,Y}--> Ext X ⊗ᴸ_B Ext Y --(ĝ ⊗ᴸ 𝟙)--> G ⊗ᴸ_B Ext Y`,

where `ĝ = Ext(g) ≫ ε_G` is the transpose of `g`.  So `ω` composed with anything landing in it is
`ν` tensored with a transpose: the unit and the counit of [stacks 0GMT] have both been removed.

This is `Dualizing.derivedTensorBaseChangeSection_naturality` moving `Ext(g ⊗ᴸ 𝟙_Y)` across `ν`,
and nothing else. -/
theorem tensor_map_comp_canonicalProjInv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    {X Y : DerivedCategory (ModuleCat.{max u v} A)}
    {G : DerivedCategory (ModuleCat.{max u v} B)}
    (g : X ⟶ (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := (X, Y))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, Y))
          (g, 𝟙 Y) ≫
        canonicalProjInv.{u, v} φ E Y G =
      (modelAdjunction.{u, v} φ E).homEquiv
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (X, Y))
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
          (G, E.functor.obj Y))
        (derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E) X Y ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
            (X := (E.functor.obj X, E.functor.obj Y))
            (Y := (G, E.functor.obj Y))
            (E.functor.map g ≫ (modelAdjunction.{u, v} φ E).counit.app G,
              𝟙 (E.functor.obj Y))) := by
  have hsec := derivedTensorBaseChangeSection_naturality.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E) g (𝟙 Y)
  simp only [CategoryTheory.Functor.map_id] at hsec
  have hkey :
      E.functor.map ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            ((g, 𝟙 Y) :
              (X, Y) ⟶ ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, Y))) ≫
          (derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) Y ≫
            (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
              (X := (E.functor.obj
                  ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
                E.functor.obj Y))
              (Y := (G, E.functor.obj Y))
              ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj Y))) =
        derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E) X Y ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
            (X := (E.functor.obj X, E.functor.obj Y))
            (Y := (G, E.functor.obj Y))
            (E.functor.map g ≫ (modelAdjunction.{u, v} φ E).counit.app G,
              𝟙 (E.functor.obj Y)) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hsec]
    refine (Category.assoc _ _ _).trans ?_
    rw [DerivedHomAdjunction.tensor_map_comp, Category.comp_id]
  dsimp only [canonicalProjInv]
  rw [← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_naturality_left, hkey]
  rfl

/-! ### The structure map as the canonical projection morphism along the unit -/

/-- **The section of the lax monoidal structure map is the canonical projection morphism
restricted along the unit of [stacks 0GMT].**  Writing `η` for that unit, `i_*` for derived
restriction of scalars and `Ext` for the model `E`,

`η_M ⊗ᴸ 𝟙_Y` followed by `ω_{Ext M, Y}` is `η_{M ⊗ᴸ_A Y}` followed by `i_*(ν_{M,Y})`.

The counit in `ω` is cancelled against `Ext η_M` by the other triangle identity, after the
naturality `Dualizing.derivedTensorBaseChangeSection_naturality` of `ν` has moved
`Ext(η_M ⊗ᴸ 𝟙_Y)` across it. -/
theorem unit_tensor_comp_canonicalProjInv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (M Y : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := (M, Y))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (E.functor.obj M), Y))
          ((modelAdjunction.{u, v} φ E).unit.app M, 𝟙 Y) ≫
        canonicalProjInv.{u, v} φ E Y (E.functor.obj M) =
      (modelAdjunction.{u, v} φ E).unit.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y)) ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
            M Y) := by
  rw [tensor_map_comp_canonicalProjInv.{u, v} φ E ((modelAdjunction.{u, v} φ E).unit.app M)]
  simp only [Functor.id_obj, Adjunction.left_triangle_components,
    Adjunction.homEquiv_unit]
  rw [DerivedHomAdjunction.tensor_map_id, Category.comp_id]

/-! ### The residue of [stacks 0E2H] with no adjunction in it -/

/-- **The coherence of the structure map that [stacks 0E2H] is waiting for**, with the
transposition carried out.  Writing `Ext` for the model `E`, `ε` for the counit of [stacks 0GMT],
`T = i_*(1_B)` for the algebra, `c_N` for
`Dualizing.ProjectionFormula.canonicalRestrictExtendInv` and `ν` for
`Dualizing.derivedTensorBaseChangeSection`, this is the equation

`Ext(c_{M ⊗ᴸ Y}) ≫ ε ≫ ν_{M,Y} = Ext(r) ≫ ν_{M ⊗ᴸ T, Y} ≫ ((Ext(c_M) ≫ ε) ⊗ᴸ 𝟙_{Ext Y})`

of morphisms `Ext((M ⊗ᴸ_A Y) ⊗ᴸ_A T) ⟶ Ext M ⊗ᴸ_B Ext Y` in `D(B)`, where `r` is the symmetry and
associativity rearrangement `(M ⊗ᴸ Y) ⊗ᴸ T ⟶ (M ⊗ᴸ T) ⊗ᴸ Y` of [stacks 0A63] that
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` carries.

Neither adjunction occurs: no unit of [stacks 0GMT], no derived restriction of scalars, no
transposition and no internal Hom.  Only `ν`, the counit, and the symmetric monoidal structure of
[stacks 0A63].  It is equivalent to
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` by
`Dualizing.ProjectionFormula.canonicalProjTensorBaseChangeCompat_iff_coherence`, and this is the
smallest shape the second input of [stacks 0E2H] has been reduced to. -/
def CanonicalTensorBaseChangeCoherence (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A)) : Prop :=
  E.functor.map (canonicalRestrictExtendInv.{u, v} φ E
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y))) ≫
      (modelAdjunction.{u, v} φ E).counit.app
          (E.functor.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y))) ≫
        derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E) M Y =
    E.functor.map
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
              (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y),
                restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
              (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (Y, M),
                restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
              (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap M Y).hom,
                𝟙 (restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) ≫
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y M
              (restrictedAlgebra.{u, max u v}
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
                (M, restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))).hom) ≫
      derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (M, restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) Y ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
          (X := (E.functor.obj
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
                (M, restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)),
            E.functor.obj Y))
          (Y := (E.functor.obj M, E.functor.obj Y))
          (E.functor.map (canonicalRestrictExtendInv.{u, v} φ E M) ≫
              (modelAdjunction.{u, v} φ E).counit.app (E.functor.obj M),
            𝟙 (E.functor.obj Y))

/-- **The second input of [stacks 0E2H] is a coherence of `ν` in `D(B)` alone.**  Both sides of
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` are transposes over
[stacks 0GMT]: the left-hand side by
`Dualizing.ProjectionFormula.comp_map_eq_homEquiv`, since it is a morphism into a restriction
followed by the restriction of `ν`; the right-hand side by
`Dualizing.ProjectionFormula.tensor_map_comp_canonicalProjInv`, which rewrites the one canonical
projection morphism it contains.  Transposition is a bijection, so the coherence is exactly
`Dualizing.ProjectionFormula.CanonicalTensorBaseChangeCoherence`.

Unconditional: no coherence is assumed. -/
theorem canonicalProjTensorBaseChangeCompat_iff_coherence (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A)) :
    CanonicalProjTensorBaseChangeCompat.{u, v} φ E Y M ↔
      CanonicalTensorBaseChangeCoherence.{u, v} φ E Y M := by
  dsimp only [CanonicalProjTensorBaseChangeCompat, CanonicalTensorBaseChangeCoherence]
  rw [comp_map_eq_homEquiv (modelAdjunction.{u, v} φ E),
    tensor_map_comp_canonicalProjInv.{u, v} φ E (canonicalRestrictExtendInv.{u, v} φ E M),
    ← Adjunction.homEquiv_naturality_left]
  exact Equiv.apply_eq_iff_eq _

end ProjectionFormula

end Dualizing

end
