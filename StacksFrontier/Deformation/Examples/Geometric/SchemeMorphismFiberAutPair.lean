module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationFiberAut
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The automorphisms of a deformation of a morphism are the compatible pairs

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` and let `M` be a deformation of `f`
in the sense of [Stacks Project, Tag 0E3T]. The proof of [Stacks Project, Tag 0E3V] opens by
identifying the automorphism group of the trivial deformation

`f' : X' = X ×_{Spec k} Spec k[ε] ⟶ Y' = Y ×_{Spec k} Spec k[ε]`

with the pairs `(α, β)` of automorphisms of the two endpoint deformations that are **compatible
with `f'`**, i.e. that satisfy `f' ∘ α = β ∘ f'`. This file proves that sentence, for an
arbitrary deformation of `f` over an arbitrary object of `𝒞_Λ` rather than only for the trivial
deformation over the dual numbers.

## Main definitions

* `Deformation.Examples.morphismDeformationFiberObj`: a deformation of `f` read as an object of
  the fibre of the projection to `𝒞_Λ` over its own base object.
* `Deformation.Examples.morphismFiberAutEquivSelfMapPairs`: an automorphism of that fibre object
  is exactly a pair of invertible self-maps of the two total spaces, the second over the base,
  both fixing the two special-fibre immersions, and commuting with the arrow of the family.
* `Deformation.Examples.morphismFiberAutPair`: the resulting map
  `Aut(M) → Aut(source M) × Aut(target M)` on fibre automorphism groups.

## Main results

* `Deformation.Examples.morphismFiberHom_comm`: the two components of an arrow of the fibre
  commute with the arrow of the family. This is the source's `f' ∘ α = β ∘ f'`.
* `Deformation.Examples.morphismFiberAutPair_fst_map` and
  `Deformation.Examples.morphismFiberAutPair_snd_map`: the pair map is the map induced by the
  two endpoint-forgetting functors, so it is not an arbitrary reparametrisation.
* `Deformation.Examples.exists_morphismFiberAutPair_eq_iff`: **the opening sentence of the proof
  of [Stacks Project, Tag 0E3V]**. A pair of automorphisms of the two endpoint deformations is
  in the image of the pair map exactly when it commutes with the arrow of the family. For the
  trivial deformation of `f` over the dual numbers this is the source's "pairs `(α, β)` of
  infinitesimal automorphisms of `X` and `Y` compatible with `f'`".
* `Deformation.Examples.injective_morphismFiberAutPair`: a fibre automorphism of a deformation
  of `f` is determined by its two endpoint components.

## Implementation notes

The composition of `Deformation.Examples.SchemeMorphismFamily.Hom` is **contravariant** on the
two total spaces: an arrow of families points covariantly on bases and contravariantly on
sources and targets. So the two components of a fibre automorphism compose in the order opposite
to the group law, exactly as in `Deformation.Examples.fiberAutEquivSelfMaps_mul`, and the
invertibility of each component is read off the two identities of the automorphism in that
order.

The `source_pullback` field of an arrow of families is a *cartesian* square, not merely a
commuting one. For an arrow whose two total-space components are invertible it is automatic: a
square of schemes whose two vertical arrows are isomorphisms is cartesian. Likewise
`target_pullback` becomes the statement that the target component is invertible over the base
once the component on base objects is the identity, because `Deformation.Examples.baseSpecMap`
of an identity is an identity. Both directions of the bijection therefore carry only the data
listed in the subtype, and no cartesianness has to be supplied by a caller.

That the **source** component is over the base is not part of the subtype: it follows from the
other clauses. The commuting square `M.morphism ≫ β = α ≫ M.morphism` and the factorisation
`M.morphism ≫ M.targetToBase = M.sourceToBase` of
`Deformation.Examples.SchemeMorphismFamily.over_base` give
`α ≫ sourceToBase = α ≫ M.morphism ≫ targetToBase = M.morphism ≫ β ≫ targetToBase =
sourceToBase`, so it is derived where the endpoint reading needs it.

The two endpoint deformations are taken as the values of
`Deformation.Examples.schemeMorphismSourceForgetful` and
`Deformation.Examples.schemeMorphismTargetForgetful` at `M`, whose total space, structure
morphism and special-fibre immersion are the corresponding fields of `M` by `rfl`. This is what
makes the clauses of the subtype of
`Deformation.Examples.fiberAutEquivSelfMaps` at those deformations the clauses proved here, with
no transport.

The component of an arrow of the fibre on base objects is read through
`CategoryTheory.Functor.IsHomLift.fac'`, whose right-hand side is a composite of two `eqToHom`s
that `simp` collapses, rather than through `CategoryTheory.Functor.IsHomLift.eq_of_isHomLift`:
the projection to `𝒞_Λ` of the deformation category of a morphism is built from
`Deformation.objectsOverFunctor`, so `p.obj M` is not *reducibly* `M.left.base` and instance
search for the lifting condition does not fire at the latter spelling. The equation is then
transported by a `have` with a declared type, which crosses the identification where `rw`
refuses the motive.

No `@[stacks 0E3V]` attribute is carried: this is the first sentence of the source's proof, not
a clause of its statement. The arrow `a` of the source's sequence is
`Deformation.Examples.schemeMorphismInfinitesimalPair`, which is stated on the tangent spaces of
the automorphism functors rather than on these automorphism groups.

## References

* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The fibre of the projection to `𝒞_Λ` -/

/-- A deformation of `f` read as an object of the fibre of the projection to `𝒞_Λ` over its own
base object. -/
abbrev morphismDeformationFiberObj (M : schemeMorphismDeformationCategory f pX pY hf) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber M.left.base :=
  ⟨M, rfl⟩

/-- An arrow of the fibre acts as the identity on the base object of the family: the lifting
condition expresses its component on bases as a composite of two identifications of that object
with itself. -/
theorem morphismDeformationFiberHom_base
    {M : schemeMorphismDeformationCategory f pX pY hf}
    (g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M) :
    g.val.left.base = 𝟙 M.left.base := by
  have := g.2
  have hfac := IsHomLift.fac' (schemeMorphismDeformationCategoryProjection f pX pY hf)
    (𝟙 M.left.base) g.val
  have h2 : g.val.left.base =
      eqToHom (morphismDeformationFiberObj f pX pY hf M).2 ≫ 𝟙 M.left.base ≫
        eqToHom (morphismDeformationFiberObj f pX pY hf M).2.symm := hfac
  rw [h2, Category.id_comp, eqToHom_trans]
  exact eqToHom_refl _ _

/-- A self-arrow of a deformation of `f` whose component on bases is the identity is an arrow of
the fibre over that base object. -/
theorem morphismDeformationFiberHom_isHomLift
    {M : schemeMorphismDeformationCategory f pX pY hf} (g : M ⟶ M)
    (hg : g.left.base = 𝟙 M.left.base) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).IsHomLift (𝟙 M.left.base) g := by
  refine IsHomLift.of_fac' _ (𝟙 M.left.base) g rfl rfl ?_
  simp only [Category.id_comp]
  exact hg

/-! ### The clauses satisfied by an arrow of the fibre -/

section Clauses

variable {M : schemeMorphismDeformationCategory f pX pY hf}

/-- The target component of an arrow of the fibre is over the structure morphism of the target:
the `target_pullback` field of the arrow, read with its component on bases the identity. -/
theorem morphismFiberHom_target_comp_toBase
    (g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M) :
    g.val.left.target ≫ M.left.targetToBase = M.left.targetToBase := by
  have hw := g.val.left.target_pullback.w
  rw [morphismDeformationFiberHom_base f pX pY hf g, baseSpecMap_id, Category.comp_id] at hw
  exact hw

/-- The source component of an arrow of the fibre fixes the special-fibre immersion of the
source: the source component of the arrow down to the special fibre. -/
theorem morphismFiberHom_source_special
    (g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M) :
    M.hom.source ≫ g.val.left.source = M.hom.source :=
  congrArg SchemeMorphismFamily.Hom.source (Over.w g.val)

/-- The target component of an arrow of the fibre fixes the special-fibre immersion of the
target: the target component of the arrow down to the special fibre. -/
theorem morphismFiberHom_target_special
    (g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M) :
    M.hom.target ≫ g.val.left.target = M.hom.target :=
  congrArg SchemeMorphismFamily.Hom.target (Over.w g.val)

/-- **The two components of an arrow of the fibre commute with the arrow of the family.** This is
the source's `f' ∘ α = β ∘ f'`: the commuting square underlying the `source_pullback` field. -/
theorem morphismFiberHom_comm
    (g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M) :
    M.left.morphism ≫ g.val.left.target = g.val.left.source ≫ M.left.morphism :=
  g.val.left.source_pullback.w

/-- The source component of a fibre automorphism is invertible, its inverse being the source
component of the inverse automorphism. The composition of arrows of families is contravariant on
sources, so the two identities of the automorphism give the two identities of the component in
the opposite order. -/
theorem morphismFiberAut_source_isIso (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    IsIso a.asIso.hom.val.left.source :=
  ⟨a.asIso.inv.val.left.source,
    congrArg (fun g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M => g.val.left.source) a.asIso.inv_hom_id,
    congrArg (fun g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M => g.val.left.source) a.asIso.hom_inv_id⟩

/-- The target component of a fibre automorphism is invertible, its inverse being the target
component of the inverse automorphism. -/
theorem morphismFiberAut_target_isIso (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    IsIso a.asIso.hom.val.left.target :=
  ⟨a.asIso.inv.val.left.target,
    congrArg (fun g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M => g.val.left.target) a.asIso.inv_hom_id,
    congrArg (fun g : morphismDeformationFiberObj f pX pY hf M ⟶
      morphismDeformationFiberObj f pX pY hf M => g.val.left.target) a.asIso.hom_inv_id⟩

/-- The source component of a compatible pair is over the base: it is not part of the data of
`Deformation.Examples.morphismFiberAutEquivSelfMapPairs`, because the commuting square and the
factorisation of the structure morphism of the source through the arrow of the family already
force it. -/
theorem morphismFiberPair_fst_comp_sourceToBase
    {α : M.left.source ⟶ M.left.source} {β : M.left.target ⟶ M.left.target}
    (hβb : β ≫ M.left.targetToBase = M.left.targetToBase)
    (hcomm : M.left.morphism ≫ β = α ≫ M.left.morphism) :
    α ≫ M.left.sourceToBase = M.left.sourceToBase := by
  calc α ≫ M.left.sourceToBase
      = α ≫ M.left.morphism ≫ M.left.targetToBase := by rw [M.left.over_base]
    _ = (M.left.morphism ≫ β) ≫ M.left.targetToBase := by
        rw [← Category.assoc, ← hcomm]
    _ = M.left.morphism ≫ M.left.targetToBase := by rw [Category.assoc, hβb]
    _ = M.left.sourceToBase := M.left.over_base

end Clauses

/-! ### Fibre automorphisms as pairs of self-maps -/

/-- **An automorphism of a deformation of `f` in its fibre is exactly a compatible pair of
invertible self-maps of its two total spaces.** The `target_pullback` field of an arrow of
families lying over the identity of the base object says that the target component is invertible
over the structure morphism of the target; the `source_pullback` field says that the square
formed by the two components and the arrow of the family is cartesian, which for invertible
components is just that it commutes; and the two components of the arrow down to the special
fibre say that the two self-maps fix the two special-fibre immersions. -/
def morphismFiberAutEquivSelfMapPairs (M : schemeMorphismDeformationCategory f pX pY hf) :
    Aut (morphismDeformationFiberObj f pX pY hf M) ≃
      { p : (M.left.source ⟶ M.left.source) × (M.left.target ⟶ M.left.target) //
        IsIso p.1 ∧ IsIso p.2 ∧
          p.2 ≫ M.left.targetToBase = M.left.targetToBase ∧
          M.hom.source ≫ p.1 = M.hom.source ∧
          M.hom.target ≫ p.2 = M.hom.target ∧
          M.left.morphism ≫ p.2 = p.1 ≫ M.left.morphism } where
  toFun a :=
    ⟨(a.asIso.hom.val.left.source, a.asIso.hom.val.left.target),
      morphismFiberAut_source_isIso f pX pY hf a, morphismFiberAut_target_isIso f pX pY hf a,
      morphismFiberHom_target_comp_toBase f pX pY hf a.asIso.hom,
      morphismFiberHom_source_special f pX pY hf a.asIso.hom,
      morphismFiberHom_target_special f pX pY hf a.asIso.hom,
      morphismFiberHom_comm f pX pY hf a.asIso.hom⟩
  invFun := fun ⟨p, hα, hβ, hβb, hsα, hsβ, hcomm⟩ => by
    letI := hα
    letI := hβ
    have hβb' : CategoryTheory.inv p.2 ≫ M.left.targetToBase = M.left.targetToBase := by
      calc CategoryTheory.inv p.2 ≫ M.left.targetToBase
          = CategoryTheory.inv p.2 ≫ p.2 ≫ M.left.targetToBase := by rw [hβb]
        _ = M.left.targetToBase := by
            rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    have hsα' : M.hom.source ≫ CategoryTheory.inv p.1 = M.hom.source := by
      calc M.hom.source ≫ CategoryTheory.inv p.1
          = (M.hom.source ≫ p.1) ≫ CategoryTheory.inv p.1 := by rw [hsα]
        _ = M.hom.source := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hsβ' : M.hom.target ≫ CategoryTheory.inv p.2 = M.hom.target := by
      calc M.hom.target ≫ CategoryTheory.inv p.2
          = (M.hom.target ≫ p.2) ≫ CategoryTheory.inv p.2 := by rw [hsβ]
        _ = M.hom.target := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hcomm' : M.left.morphism ≫ CategoryTheory.inv p.2 =
        CategoryTheory.inv p.1 ≫ M.left.morphism := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact hcomm.symm
    let mk : ∀ (α : M.left.source ⟶ M.left.source) (β : M.left.target ⟶ M.left.target),
        IsIso α → IsIso β → β ≫ M.left.targetToBase = M.left.targetToBase →
        M.left.morphism ≫ β = α ≫ M.left.morphism → (M.left ⟶ M.left) :=
      fun α β hiα hiβ hb hc =>
        { base := 𝟙 M.left.base
          source := α
          target := β
          source_pullback := by
            let := hiα
            let := hiβ
            exact IsPullback.of_vert_isIso ⟨hc⟩
          target_pullback := by
            let := hiβ
            rw [baseSpecMap_id]
            exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hb⟩ }
    let hom : M ⟶ M := Over.homMk (mk p.1 p.2 hα hβ hβb hcomm)
      (SchemeMorphismFamily.Hom.ext (Category.id_comp _) hsα hsβ)
    let inv : M ⟶ M :=
      Over.homMk (mk (CategoryTheory.inv p.1) (CategoryTheory.inv p.2)
          (IsIso.inv_isIso) (IsIso.inv_isIso) hβb' hcomm')
        (SchemeMorphismFamily.Hom.ext (Category.id_comp _) hsα' hsβ')
    refine .of
      { hom := ⟨hom, morphismDeformationFiberHom_isHomLift f pX pY hf hom rfl⟩
        inv := ⟨inv, morphismDeformationFiberHom_isHomLift f pX pY hf inv rfl⟩
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · refine Functor.Fiber.hom_ext (show hom ≫ inv = 𝟙 M from ?_)
      refine Over.OverMorphism.ext (SchemeMorphismFamily.Hom.ext ?_ ?_ ?_)
      · exact Category.comp_id _
      · exact IsIso.inv_hom_id p.1
      · exact IsIso.inv_hom_id p.2
    · refine Functor.Fiber.hom_ext (show inv ≫ hom = 𝟙 M from ?_)
      refine Over.OverMorphism.ext (SchemeMorphismFamily.Hom.ext ?_ ?_ ?_)
      · exact Category.comp_id _
      · exact IsIso.hom_inv_id p.1
      · exact IsIso.hom_inv_id p.2
  left_inv a := by
    refine Aut.ext (Iso.ext (Subtype.ext (Over.OverMorphism.ext
      (SchemeMorphismFamily.Hom.ext ?_ rfl rfl))))
    exact (morphismDeformationFiberHom_base f pX pY hf a.asIso.hom).symm
  right_inv := by
    rintro ⟨p, hα, hβ, hβb, hsα, hsβ, hcomm⟩
    exact Subtype.ext rfl

/-- The forward direction of `Deformation.Examples.morphismFiberAutEquivSelfMapPairs` is the
pair of the two total-space components. -/
@[simp]
theorem morphismFiberAutEquivSelfMapPairs_apply
    (M : schemeMorphismDeformationCategory f pX pY hf)
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    (morphismFiberAutEquivSelfMapPairs f pX pY hf M a).val =
      (a.asIso.hom.val.left.source, a.asIso.hom.val.left.target) := rfl

/-! ### Fibre automorphisms as pairs of endpoint automorphisms -/

/-- **The pair map on fibre automorphism groups**, `Aut(M) → Aut(source M) × Aut(target M)`:
the two total-space components of a fibre automorphism, read as automorphisms of the two
endpoint deformations in their own fibres through
`Deformation.Examples.fiberAutEquivSelfMaps`. -/
def morphismFiberAutPair {M : schemeMorphismDeformationCategory f pX pY hf}
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    Aut (deformationFiberObj ((schemeMorphismSourceForgetful f pX pY hf).obj M)) ×
      Aut (deformationFiberObj ((schemeMorphismTargetForgetful f pX pY hf).obj M)) :=
  ((fiberAutEquivSelfMaps ((schemeMorphismSourceForgetful f pX pY hf).obj M)).symm
      ⟨a.asIso.hom.val.left.source,
        morphismFiberPair_fst_comp_sourceToBase f pX pY hf
          (morphismFiberHom_target_comp_toBase f pX pY hf a.asIso.hom)
          (morphismFiberHom_comm f pX pY hf a.asIso.hom),
        morphismFiberHom_source_special f pX pY hf a.asIso.hom,
        morphismFiberAut_source_isIso f pX pY hf a⟩,
    (fiberAutEquivSelfMaps ((schemeMorphismTargetForgetful f pX pY hf).obj M)).symm
      ⟨a.asIso.hom.val.left.target,
        morphismFiberHom_target_comp_toBase f pX pY hf a.asIso.hom,
        morphismFiberHom_target_special f pX pY hf a.asIso.hom,
        morphismFiberAut_target_isIso f pX pY hf a⟩)

/-- The first component of the pair map is the source component of the fibre automorphism, read
as a self-map of the total space. -/
@[simp]
theorem morphismFiberAutPair_fst_val {M : schemeMorphismDeformationCategory f pX pY hf}
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    (fiberAutEquivSelfMaps ((schemeMorphismSourceForgetful f pX pY hf).obj M)
        (morphismFiberAutPair f pX pY hf a).1).val = a.asIso.hom.val.left.source :=
  congrArg Subtype.val ((fiberAutEquivSelfMaps
    ((schemeMorphismSourceForgetful f pX pY hf).obj M)).apply_symm_apply _)

/-- The second component of the pair map is the target component of the fibre automorphism, read
as a self-map of the total space. -/
@[simp]
theorem morphismFiberAutPair_snd_val {M : schemeMorphismDeformationCategory f pX pY hf}
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    (fiberAutEquivSelfMaps ((schemeMorphismTargetForgetful f pX pY hf).obj M)
        (morphismFiberAutPair f pX pY hf a).2).val = a.asIso.hom.val.left.target :=
  congrArg Subtype.val ((fiberAutEquivSelfMaps
    ((schemeMorphismTargetForgetful f pX pY hf).obj M)).apply_symm_apply _)

/-- **The pair map is the map induced by the source-forgetting functor.** The self-map of the
total space underlying the first component of the pair is the total-space component of the image
of the automorphism under `Deformation.Examples.schemeMorphismSourceForgetful`, so the pair map
is not an arbitrary reparametrisation. -/
theorem morphismFiberAutPair_fst_map {M : schemeMorphismDeformationCategory f pX pY hf}
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    (fiberAutEquivSelfMaps ((schemeMorphismSourceForgetful f pX pY hf).obj M)
        (morphismFiberAutPair f pX pY hf a).1).val =
      ((schemeMorphismSourceForgetful f pX pY hf).map a.asIso.hom.val).map :=
  morphismFiberAutPair_fst_val f pX pY hf a

/-- **The pair map is the map induced by the target-forgetting functor.** -/
theorem morphismFiberAutPair_snd_map {M : schemeMorphismDeformationCategory f pX pY hf}
    (a : Aut (morphismDeformationFiberObj f pX pY hf M)) :
    (fiberAutEquivSelfMaps ((schemeMorphismTargetForgetful f pX pY hf).obj M)
        (morphismFiberAutPair f pX pY hf a).2).val =
      ((schemeMorphismTargetForgetful f pX pY hf).map a.asIso.hom.val).map :=
  morphismFiberAutPair_snd_val f pX pY hf a

/-- **The image of the pair map consists exactly of the pairs commuting with the arrow of the
family.** This is the opening sentence of the proof of [Stacks Project, Tag 0E3V]: an
automorphism of a deformation of `f` "is clearly the same thing as" a pair of automorphisms of
the two endpoint deformations compatible with the arrow.

For the trivial deformation of `f` over the dual numbers the two sides are the source's
`Inf(𝓓_{X ⟶ Y})` and the pairs `(α, β)` of infinitesimal automorphisms of `X` and `Y` with
`f' ∘ α = β ∘ f'`. -/
theorem exists_morphismFiberAutPair_eq_iff
    (M : schemeMorphismDeformationCategory f pX pY hf)
    (q : Aut (deformationFiberObj ((schemeMorphismSourceForgetful f pX pY hf).obj M)) ×
      Aut (deformationFiberObj ((schemeMorphismTargetForgetful f pX pY hf).obj M))) :
    (∃ a, morphismFiberAutPair f pX pY hf a = q) ↔
      M.left.morphism ≫
          (fiberAutEquivSelfMaps
            ((schemeMorphismTargetForgetful f pX pY hf).obj M) q.2).val =
        (fiberAutEquivSelfMaps
            ((schemeMorphismSourceForgetful f pX pY hf).obj M) q.1).val ≫
          M.left.morphism := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [morphismFiberAutPair_fst_val, morphismFiberAutPair_snd_val]
    exact morphismFiberHom_comm f pX pY hf a.asIso.hom
  · intro hq
    set eS := fiberAutEquivSelfMaps ((schemeMorphismSourceForgetful f pX pY hf).obj M)
    set eT := fiberAutEquivSelfMaps ((schemeMorphismTargetForgetful f pX pY hf).obj M)
    refine ⟨(morphismFiberAutEquivSelfMapPairs f pX pY hf M).symm
      ⟨((eS q.1).val, (eT q.2).val), (eS q.1).2.2.2, (eT q.2).2.2.2,
        (eT q.2).2.1, (eS q.1).2.2.1, (eT q.2).2.2.1, hq⟩, ?_⟩
    exact Prod.ext (eS.injective (Subtype.ext (morphismFiberAutPair_fst_val f pX pY hf _)))
      (eT.injective (Subtype.ext (morphismFiberAutPair_snd_val f pX pY hf _)))

/-- **The pair map is injective**: a fibre automorphism of a deformation of `f` is determined by
its two endpoint components. This is the geometric form of the exactness of
`0 → Inf(𝓓_{X ⟶ Y}) → Inf(𝓓_X × 𝓓_Y)` asserted at the first spot of the sequence of
[Stacks Project, Tag 0E3V]. -/
theorem injective_morphismFiberAutPair
    (M : schemeMorphismDeformationCategory f pX pY hf) :
    Function.Injective
      (morphismFiberAutPair f pX pY hf (M := M)) := by
  intro a b hab
  have h₁ : a.asIso.hom.val.left.source = b.asIso.hom.val.left.source := by
    rw [← morphismFiberAutPair_fst_val f pX pY hf a,
      ← morphismFiberAutPair_fst_val f pX pY hf b, hab]
  have h₂ : a.asIso.hom.val.left.target = b.asIso.hom.val.left.target := by
    rw [← morphismFiberAutPair_snd_val f pX pY hf a,
      ← morphismFiberAutPair_snd_val f pX pY hf b, hab]
  exact (morphismFiberAutEquivSelfMapPairs f pX pY hf M).injective (Subtype.ext (Prod.ext h₁ h₂))

end Deformation.Examples

end
