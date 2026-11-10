module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyProductAffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHom
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetFromCoversTop
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransportHomPair

/-!
# Stacks 0GQZ for a quasi-compact and quasi-separated algebraic stack

`AlgebraicGeometry.FibredSite.isIso_colimit_post_hom_of_isFinitePresentation` proves, for a
category fibred in groupoids `𝒳` over the big fppf category of `S` whose total category is
essentially small, that `Hom_𝒳(𝒢, -)` commutes with filtered colimits for `𝒢` of finite
presentation, granted the condition `hX` of **Stacks 0GMR** part (4) for the equi-universe model
of the fppf site of `𝒳`.
This file discharges `hX` when `𝒳` is a quasi-compact algebraic stack which is quasi-separated over
a quasi-separated base, exactly as the source does: through **Stacks 0GMS** case (2), with the
objects of the model lying over affine schemes as the collection `B` of that case. The result is
**Stacks 0GQZ** with no hypothesis beyond the tag's own.

## Main definitions

* `AlgebraicGeometry.Stack.FppfModel.affineObjects`: the objects of the model whose image in the
  fppf site lies over an affine scheme.

## Main results

* `AlgebraicGeometry.FibredSite`
  `.isIso_colimit_post_hom_quasicoherent_of_isFinitePresentation_without_inclusionColimits`: the
  quasi-coherent clause of the engine, with the colimit clause of **Stacks 06WV** (4) used rather
  than assumed.
* `AlgebraicGeometry.Stack.fppfTopology_changeBaseFiberedInGroupoids`: the fppf site of a
  category fibred in groupoids does not depend on the base it is viewed over.
* `AlgebraicGeometry.Stack.exists_affineObject_exists_covering_hom_pair_of_isQuasiSeparatedAbs`:
  the hom-set form of condition (2)(c) of Stacks 0GMS for a quasi-separated algebraic stack.
* `AlgebraicGeometry.Stack.FppfModel.exists_finite_affineObjects_isLocallySurjective`,
  `…exists_finite_affineObjects_hypercover_hom` and
  `…exists_finite_affineObjects_isLocallySurjective_prodLift`: conditions (2)(a), (2)(b) and
  (2)(c) of Stacks 0GMS on the model.
* `AlgebraicGeometry.Stack.FppfModel.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`:
  the condition of Stacks 0GMR part (4) for the model, which is `hX` discharged.
* `AlgebraicGeometry.Stack.isIso_colimit_post_hom_of_isQuasiCompactStack`: **Stacks 0GQZ**, the
  displayed colimit equality.
* `AlgebraicGeometry.Stack.isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack`:
  **Stacks 0GQZ**, the "in particular" clause for `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.isIso_colimit_post_hom_and_quasicoherent_of_isQuasiCompactStack`:
  **Stacks 0GQZ** in full, the conjunction of the two.

## Implementation notes

The index type of the one-element families of conditions (2)(a) and (2)(c) has to lie in
`Type u`, which is where Stacks 0GMS case (2) wants it, so it is `PUnit.{u + 1}`;
`CategoryTheory.GrothendieckTopology.coversTop_punit` moves the one of (2)(a) down from the
`Type (u + 2)` at which `CategoryTheory.GrothendieckTopology.coversTop_inverse_obj` leaves it.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
* [Stacks Project, Tag 0GQZ](https://stacks.math.columbia.edu/tag/0GQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FibredSite

universe u v w

/-! ### Stacks 0GQZ on the fppf site of an algebraic stack

The fppf site of a category fibred in groupoids over the big fppf category of `S` has its objects
in `Type (u + 1)` and its morphisms in `Type u`; that is the shape the fppf site of an algebraic
stack has, and the shape in which the sheafification hypotheses of
`SheafOfModules.IsFinitePresentation` are already available on the slices
(`AlgebraicGeometry.FibredSite.hasSheafify_associatedTopology_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology_over`). Both are pinned
as local instances below, which is what lets `𝒢` be assumed of finite presentation *on the fppf
site itself* rather than on the model. -/

section FppfSiteOfStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS)

attribute [local instance] hasSheafify_associatedTopology_over
  wEqualsLocallyBijective_associatedTopology_over

/-- **Stacks 0GQZ for quasi-coherent modules.** The same comparison, for a filtered colimit taken
in the category `QCoh(𝒪_𝒳)` of Stacks 06WG rather than in all `𝒪_𝒳`-modules.

Beyond the hypothesis `hX` of
`AlgebraicGeometry.FibredSite.isIso_colimit_post_hom_of_isFinitePresentation` nothing is carried.
The source deduces this clause from the colimit clause of Stacks 06WV (4) — that colimits of
quasi-coherent modules agree with colimits of all modules — and that clause is available for the
fppf site of a category fibred in groupoids as
`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion'`, so it is used
here rather than assumed.

Like the clause for all modules this carries `hX`; for a quasi-compact and quasi-separated
algebraic stack `hX` is discharged in
`AlgebraicGeometry.Stack.isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack`. -/
theorem isIso_colimit_post_hom_quasicoherent_of_isFinitePresentation_without_inclusionColimits
    (hp : p.IsFiberedInGroupoids) (G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
    (hG : G.obj.IsFinitePresentation)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
    (hX : ∃ T : Set (Sheaf (fppfModelRingedSite B S hS p hp).J (Type u)),
      (∀ H : Sheaf (fppfModelRingedSite B S hS p hp).J (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L))
    [HasColimit D] [HasColimit (D ⋙ coyoneda.obj (Opposite.op G))] :
    IsIso (colimit.post D (coyoneda.obj (Opposite.op G))) :=
  have _ : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
    preservesColimitsOfSize_quasicoherentInclusion' B S hS p hp
  have _ := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringStructureSheafCore B S hS p hp .fppf)).preservesColimitsOfShape_coyoneda_fullSubcategory
      G K (preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model
        B S hS p hp G.obj
        (isFinitePresentation_modulesEquivFppfModelModules B S hS p hp G.obj hG) K hX)
  inferInstance

end FppfSiteOfStack

end AlgebraicGeometry.FibredSite

/-! ### The fppf site does not see the base, and condition (2)(c) for an absolutely
quasi-separated stack -/

namespace AlgebraicGeometry.Stack

universe u v w w'

/-- **The fppf site of a category fibred in groupoids does not depend on the base scheme.**
Viewing `𝒳` over `S'` along a morphism `g : S ⟶ S'` of the big fppf site (Construction A of
Stacks 04X5) leaves the fppf topology of its total category unchanged: both are the topology
inherited from the ambient big fppf site along the composite with the forgetful functor, and
`Over.map g ⋙ Over.forget S' = Over.forget S` on the nose. -/
theorem fppfTopology_changeBaseFiberedInGroupoids (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    fppfTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) =
      fppfTopology B S hS 𝒳 := by
  let _ : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let _ : (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p.IsFibered :=
    (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).2.isFibered
  change (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p.inheritedTopology
      (B.topology.over (B.obj hS')) = 𝒳.val.p.inheritedTopology (B.topology.over (B.obj hS))
  rw [← Functor.inheritedTopology_comp_overForget' (B.obj hS') _ B.topology,
    ← Functor.inheritedTopology_comp_overForget' (B.obj hS) _ B.topology]
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The hom-set form of condition (2)(c) of Stacks 0GMS for the fppf site of a quasi-separated
algebraic stack.** For two objects `U`, `U'` of the site lying over affine schemes there is a
single object `V` lying over an affine scheme, with morphisms `p : V ⟶ U` and `q : V ⟶ U'`,
through which every pair of morphisms `α : y ⟶ U`, `β : y ⟶ U'` factors after passing to a
covering of `y`.

Quasi-separatedness is that of Stacks 050D part (8): quasi-separatedness over `Spec(ℤ)` of `𝒳`
viewed over `Spec(ℤ)`. No condition on the base scheme `S` is needed. The statement is
`AlgebraicGeometry.Stack.exists_affineObject_exists_covering_hom_pair` for `𝒳` viewed over the
quasi-separated (indeed affine) base `Spec(ℤ)`: viewing over `Spec(ℤ)` changes neither the
total category, nor which objects lie over affine schemes, nor, by
`AlgebraicGeometry.Stack.fppfTopology_changeBaseFiberedInGroupoids`, the fppf topology. -/
theorem exists_affineObject_exists_covering_hom_pair_of_isQuasiSeparatedAbs
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (U : 𝒳.val.val.obj) (hU : U ∈ affineObjects B S hS 𝒳.val)
    (U' : 𝒳.val.val.obj) (hU' : U' ∈ affineObjects B S hS 𝒳.val) :
    ∃ V : 𝒳.val.val.obj, V ∈ affineObjects B S hS 𝒳.val ∧
      ∃ (p : V ⟶ U) (q : V ⟶ U'),
        ∀ (y : 𝒳.val.val.obj) (α : y ⟶ U) (β : y ⟶ U'),
          ∃ T : Sieve y, T ∈ fppfTopology B S hS 𝒳.val y ∧
            ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), T.arrows g →
              ∃ r : z ⟶ V, r ≫ p = g ≫ α ∧ r ≫ q = g ≫ β := by
  have hqs : QuasiSeparatedSpace (Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  have htop := fppfTopology_changeBaseFiberedInGroupoids B S _ hS (contains_specULiftZ B)
    (toIntObject B S hS) 𝒳.val
  have h := exists_affineObject_exists_covering_hom_pair.{u, w'} B _ (contains_specULiftZ B)
    (viewOverInt.{u, w, w'} B S hS 𝒳) hqs h𝒳 U hU U' hU'
  change ∃ V : 𝒳.val.val.obj, V ∈ affineObjects B S hS 𝒳.val ∧
      ∃ (p : V ⟶ U) (q : V ⟶ U'),
        ∀ (y : 𝒳.val.val.obj) (α : y ⟶ U) (β : y ⟶ U'),
          ∃ T : Sieve y, T ∈ fppfTopology B _ (contains_specULiftZ B)
              (changeBaseFiberedInGroupoids B S _ hS (contains_specULiftZ B)
                (toIntObject B S hS) 𝒳.val) y ∧
            ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), T.arrows g →
              ∃ r : z ⟶ V, r ≫ p = g ≫ α ∧ r ≫ q = g ≫ β at h
  rwa [htop] at h

end AlgebraicGeometry.Stack

/-! ### Stacks 0GMS case (2) on the equi-universe model of the fppf site of a stack -/

namespace AlgebraicGeometry.Stack.FppfModel

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The equivalence between the equi-universe model of the fppf site of `𝒳` and that site, with
the model as the source. -/
noncomputable abbrev equiv : SmallModel.{u} 𝒳.val.val.obj ≌ 𝒳.val.val.obj :=
  Stacks.SheafOfModules.SmallModelSite.equivalence.{u} (C := 𝒳.val.val.obj)

/-- The topology of the equi-universe model of the fppf site of `𝒳`: the topology of
`AlgebraicGeometry.FibredSite.fppfModelRingedSite`, which is the one Stacks 0GN0 is applied
at. -/
noncomputable abbrev topology : GrothendieckTopology (SmallModel.{u} 𝒳.val.val.obj) :=
  Stacks.SheafOfModules.SmallModelSite.topology.{u} (fppfTopology B S hS 𝒳.val)

/-- The objects of the equi-universe model of the fppf site of `𝒳` whose image in that site lies
over an affine scheme. This is the collection `B` of Stacks 0GMS case (2), and the transport to
the model of `AlgebraicGeometry.Stack.affineObjects`. -/
noncomputable def affineObjects : Set (SmallModel.{u} 𝒳.val.val.obj) :=
  {W | IsAffineObject B S hS 𝒳.val.val.p ((equiv B S hS 𝒳).functor.obj W)}

/-- Membership in `AlgebraicGeometry.Stack.FppfModel.affineObjects` is lying over an affine scheme
after passing to the fppf site. -/
@[simp]
theorem mem_affineObjects_iff {W : SmallModel.{u} 𝒳.val.val.obj} :
    W ∈ affineObjects B S hS 𝒳 ↔
      IsAffineObject B S hS 𝒳.val.val.p ((equiv B S hS 𝒳).functor.obj W) :=
  Iff.rfl

/-- **An object of the fppf site lying over an affine scheme has an inverse image in the model
lying over an affine scheme.** The image in the fppf site of that inverse image is the given
object only up to the counit isomorphism, and lying over an affine scheme is invariant under an
isomorphism of the site, the structure functor and the passage to the underlying scheme both
carrying it to an isomorphism of schemes. -/
theorem mem_affineObjects_inverse_obj {x : 𝒳.val.val.obj}
    (hx : IsAffineObject B S hS 𝒳.val.val.p x) :
    (equiv B S hS 𝒳).inverse.obj x ∈ affineObjects B S hS 𝒳 := by
  have hiso : (equiv B S hS 𝒳).functor.obj ((equiv B S hS 𝒳).inverse.obj x) ≅ x :=
    (equiv B S hS 𝒳).counitIso.app x
  have _ : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x) := hx
  exact IsAffine.of_isIso (((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).mapIso hiso).hom)

/-! ### Condition (2)(a) -/

/-- **Condition (2)(a) of Stacks 0GMS on the equi-universe model of the fppf site.** For a
quasi-compact algebraic stack there is a finite family of objects of the model lying over affine
schemes for which `∐_j h_{U_j}^# ⟶ *` is a surjection of sheaves of sets on the model.

The family has one member, the inverse image of the affine atlas object of
`AlgebraicGeometry.Stack.exists_isAffineObject_coversTop`. That statement is a `CoversTop`, so it
transports to the model by `CategoryTheory.GrothendieckTopology.coversTop_inverse_obj`, and
`CategoryTheory.Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda` turns covering the
final object into surjectivity onto the final sheaf. -/
theorem exists_finite_affineObjects_isLocallySurjective
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → SmallModel.{u} 𝒳.val.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒳) ∧
        Sheaf.IsLocallySurjective (terminal.from
          (∐ fun i => (Sheaf.sheafifiedYoneda (topology B S hS 𝒳)).obj (U i))) := by
  obtain ⟨x, hxaff, hcov⟩ := exists_isAffineObject_coversTop B S hS 𝒳 hqc
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => (equiv B S hS 𝒳).inverse.obj x,
    fun _ => mem_affineObjects_inverse_obj B S hS 𝒳 hxaff, ?_⟩
  exact Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda _ _
    (GrothendieckTopology.coversTop_punit
      (GrothendieckTopology.coversTop_inverse_obj (equiv B S hS 𝒳) hcov))

/-! ### Condition (2)(b) -/

/-- **Condition (2)(b) of Stacks 0GMS on the equi-universe model of the fppf site.** Every
covering of an object of the model lying over an affine scheme is refined by a finite covering
family by such objects.

This is the transport of `AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`,
the sieve-level form of condition (2) of Stacks 0GN4 on the fppf site, along the model
equivalence; the transports are `CategoryTheory.Sieve.ofArrows_inverse_mem` and
`CategoryTheory.Sieve.ofArrows_inverse_le`, and the hypercover packaging the one of
`AlgebraicGeometry.Space.SmallEtaleModel.exists_finite_affine_hypercover_hom`. No
quasi-compactness or quasi-separatedness is needed. -/
theorem exists_finite_affineObjects_hypercover_hom
    (U : SmallModel.{u} 𝒳.val.val.obj) (hU : U ∈ affineObjects B S hS 𝒳)
    (𝒰 : PreZeroHypercover.{u} U) (h𝒰 : 𝒰.sieve₀ ∈ topology B S hS 𝒳 U) :
    ∃ (𝒱 : PreZeroHypercover.{u} U) (_ : 𝒱.Hom 𝒰),
      𝒱.sieve₀ ∈ topology B S hS 𝒳 U ∧ Finite 𝒱.I₀ ∧
        ∀ i, 𝒱.X i ∈ affineObjects B S hS 𝒳 := by
  classical
  have hpush : (𝒰.sieve₀).functorPushforward (equiv B S hS 𝒳).functor ∈
      fppfTopology B S hS 𝒳.val ((equiv B S hS 𝒳).functor.obj U) :=
    (((equiv B S hS 𝒳).functor).functorPushforward_mem_iff
      (topology B S hS 𝒳) (fppfTopology B S hS 𝒳.val)).2 h𝒰
  obtain ⟨n, V, f, hVaff, hcov, hle⟩ :=
    hasFiniteCoverRefinementsFrom_fppfTopology B S hS 𝒳.val hU _ hpush
  set V' : Fin n → SmallModel.{u} 𝒳.val.val.obj :=
    fun i => (equiv B S hS 𝒳).inverse.obj (V i) with hV'
  set f' : ∀ i, V' i ⟶ U := fun i => (equiv B S hS 𝒳).inverse.map (f i) ≫
    (equiv B S hS 𝒳).unitIso.inv.app U with hf'
  have hcov' : Sieve.ofArrows V' f' ∈ topology B S hS 𝒳 U :=
    Sieve.ofArrows_inverse_mem (equiv B S hS 𝒳) f hcov
  have hle' : Sieve.ofArrows V' f' ≤ 𝒰.sieve₀ :=
    Sieve.ofArrows_inverse_le (equiv B S hS 𝒳) f hle
  have hVaff' : ∀ i, V' i ∈ affineObjects B S hS 𝒳 := fun i =>
    mem_affineObjects_inverse_obj B S hS 𝒳 (hVaff i)
  have key : ∀ k : Fin n, ∃ (j : 𝒰.I₀) (h : V' k ⟶ 𝒰.X j), h ≫ 𝒰.f j = f' k := by
    intro k
    obtain ⟨Y, g, p, ⟨j⟩, hfac⟩ := hle' _ (Sieve.ofArrows_mk V' f' k)
    exact ⟨j, g, hfac⟩
  choose jj hh hw using key
  have hpre : Presieve.ofArrows (fun i : ULift.{u} (Fin n) => V' i.down)
      (fun i => f' i.down) = Presieve.ofArrows V' f' := by
    refine le_antisymm ?_ ?_
    · rintro Y g ⟨i⟩; exact ⟨i.down⟩
    · rintro Y g ⟨i⟩; exact ⟨ULift.up i⟩
  refine ⟨{ I₀ := ULift.{u} (Fin n), X := fun i => V' i.down, f := fun i => f' i.down },
    { s₀ := fun i => jj i.down, h₀ := fun i => hh i.down, w₀ := fun i => hw i.down },
    ?_, inferInstance, fun i => hVaff' i.down⟩
  change Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rwa [hpre]

/-! ### Condition (2)(c) -/

/-- **Condition (2)(c) of Stacks 0GMS on the equi-universe model of the fppf site.** For two
objects of the model lying over affine schemes there is a finite family of such objects, with a
morphism to each of the two from each member, whose sheafified representables jointly surject
onto the product of the sheafified representables of the two.

The family has one member, as in the source. Quasi-separatedness is that of Stacks 050D
part (8), and no condition on the base scheme is needed. The hom-set form of the condition on the
fppf site is
`AlgebraicGeometry.Stack.exists_affineObject_exists_covering_hom_pair_of_isQuasiSeparatedAbs`; it
transports to the model by `CategoryTheory.exists_covering_hom_pair_inverse`, and
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex`, which
holds on an arbitrary site, turns the transported form into the surjection of sheaves. -/
theorem exists_finite_affineObjects_isLocallySurjective_prodLift
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (U : SmallModel.{u} 𝒳.val.val.obj) (hU : U ∈ affineObjects B S hS 𝒳)
    (U' : SmallModel.{u} 𝒳.val.val.obj) (hU' : U' ∈ affineObjects B S hS 𝒳) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → SmallModel.{u} 𝒳.val.val.obj)
      (a : ∀ i, V i ⟶ U) (b : ∀ i, V i ⟶ U'),
      (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
        Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
          Limits.prod.lift ((Sheaf.sheafifiedYoneda (topology B S hS 𝒳)).map (a i))
            ((Sheaf.sheafifiedYoneda (topology B S hS 𝒳)).map (b i))) := by
  obtain ⟨V, hVaff, p, q, hcond⟩ :=
    exists_affineObject_exists_covering_hom_pair_of_isQuasiSeparatedAbs B S hS 𝒳 h𝒳
      ((equiv B S hS 𝒳).functor.obj U) hU ((equiv B S hS 𝒳).functor.obj U') hU'
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => (equiv B S hS 𝒳).inverse.obj V,
    fun _ => (equiv B S hS 𝒳).inverse.map p ≫ (equiv B S hS 𝒳).unitIso.inv.app U,
    fun _ => (equiv B S hS 𝒳).inverse.map q ≫ (equiv B S hS 𝒳).unitIso.inv.app U',
    fun _ => mem_affineObjects_inverse_obj B S hS 𝒳 hVaff, ?_⟩
  refine Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex _ _ _ ?_
  intro Y α β
  refine exists_covering_hom_pair_inverse (J := fppfTopology B S hS 𝒳.val)
    (J' := topology B S hS 𝒳) (equiv B S hS 𝒳) (fun _ : PUnit.{u + 1} => p)
    (fun _ => q) ?_ Y α β
  intro y a b
  obtain ⟨T, hT, hfac⟩ := hcond y a b
  refine ⟨T, hT, ?_⟩
  intro z g hg
  obtain ⟨r, hr, hr'⟩ := hfac g hg
  exact ⟨PUnit.unit, r, hr, hr'⟩

/-! ### The condition of Stacks 0GMR part (4) for the model -/

/-- **The hypothesis of Stacks 0GMR part (4) for the equi-universe model of the fppf ringed site
of a quasi-compact and quasi-separated algebraic stack**, quasi-separatedness being that of
Stacks 050D part (8), with the covering set taken, as in Stacks 0GMS case (2), to be the finite
coproducts of the sheafified representables of the objects of the model lying over affine schemes.

This is the hypothesis `hX` of
`AlgebraicGeometry.FibredSite.preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model`
(the form in which Stacks 0GN0 is applied), and the one site condition Stacks 0GQZ rests on. -/
theorem exists_set_isLocallySurjective_and_isQuasiCompact_prod_self
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳) :
    ∃ T : Set (Sheaf (topology B S hS 𝒳) (Type u)),
      (∀ H : Sheaf (topology B S hS 𝒳) (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L) :=
  Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self
    (B := affineObjects B S hS 𝒳)
    (exists_finite_affineObjects_isLocallySurjective B S hS 𝒳 hqc)
    (fun U hU 𝒰 h𝒰 => exists_finite_affineObjects_hypercover_hom B S hS 𝒳 U hU 𝒰 h𝒰)
    (fun U hU U' hU' =>
      exists_finite_affineObjects_isLocallySurjective_prodLift B S hS 𝒳 h𝒳 U hU U' hU')

end AlgebraicGeometry.Stack.FppfModel

/-! ### Stacks 0GQZ for a quasi-compact and quasi-separated algebraic stack -/

namespace AlgebraicGeometry.Stack

universe u w w'

section QuasiCompactQuasiSeparated

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FibredSite.hasSheafify_associatedTopology_over
  FibredSite.wEqualsLocallyBijective_associatedTopology_over

/-- `Hom_𝒳(𝒢, -)` preserves colimits of shape `K` for `𝒢` of finite presentation on a
quasi-compact and quasi-separated algebraic stack `𝒳`. -/
private theorem preservesColimitsOfShape_coyoneda_of_isQuasiCompactStack
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (G : _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hG : G.IsFinitePresentationOnSite)
    (K : Type u) [Category.{u} K] [IsFiltered K] :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  FibredSite.preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model
    B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids G
    (FibredSite.isFinitePresentation_modulesEquivFppfModelModules B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids G
        (_root_.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' G hG)) K
    (FppfModel.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self B S hS 𝒳 hqc h𝒳)

/-- **Stacks 0GQZ, the displayed equality.** Let `𝒳` be a quasi-compact and quasi-separated
algebraic stack over a scheme `S` contained in a big fppf site, with the fppf topology of
Stacks 06TP and the structure sheaf of Stacks 06TV. Let `𝒢` be an `𝒪_𝒳`-module of finite
presentation (Stacks 03DL (7)) and `D` a filtered system `i ↦ ℱ_i` of `𝒪_𝒳`-modules. Then

`colim_i Hom_𝒳(𝒢, ℱ_i) = Hom_𝒳(𝒢, colim_i ℱ_i)`,

in the form that the canonical comparison map out of the colimit is a bijection. Both colimits
exist (`AlgebraicGeometry.FibredSite.hasColimitsOfShape_sheafOfModules_ringStructureSheafCore`).

Quasi-separatedness is that of Stacks 050D part (8), quasi-separatedness over `Spec(ℤ)`, and no
condition is put on `S`. The index category is a small filtered category, the index set of the
source being a set of the ambient universe.

The proof is the source's. The equality is the case of Stacks 0GN0 for the fppf ringed site of
`𝒳`, applied through its equi-universe model, which is
`AlgebraicGeometry.FibredSite.preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model`
at the site hypothesis of Stacks 0GN0. That hypothesis is discharged by
`AlgebraicGeometry.Stack.FppfModel.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`
through Stacks 0GMS case (2), which is where quasi-compactness and quasi-separatedness are used. -/
@[stacks 0GQZ "the displayed colimit equality, for all 𝒪_𝒳-modules"]
theorem isIso_colimit_post_hom_of_isQuasiCompactStack
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (G : _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hG : G.IsFinitePresentationOnSite)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)) :
    letI := FibredSite.hasColimitsOfShape_sheafOfModules_ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf K
    IsIso (colimit.post D (coyoneda.obj (Opposite.op G))) :=
  let := FibredSite.hasColimitsOfShape_sheafOfModules_ringStructureSheafCore B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf K
  have _ := preservesColimitsOfShape_coyoneda_of_isQuasiCompactStack B S hS 𝒳 hqc h𝒳 G hG K
  inferInstance

/-- **Stacks 0GQZ, the "in particular" clause.** For a quasi-compact and quasi-separated algebraic
stack and an `𝒪_𝒳`-module `𝒢` of finite presentation, `Hom_𝒳(𝒢, -)` commutes with filtered
colimits taken in the category `QCoh(𝒪_𝒳)` of Stacks 06WG: for a filtered system `D` of
quasi-coherent modules the comparison map from `colim_i Hom_𝒳(𝒢, ℱ_i)` to `Hom_𝒳(𝒢, colim_i ℱ_i)`,
the colimit taken in `QCoh(𝒪_𝒳)`, is a bijection. Both colimits exist
(`AlgebraicGeometry.FibredSite.hasColimitsOfSize_quasicoherentModules'`).

`Hom_𝒳(𝒢, -)` on `QCoh(𝒪_𝒳)` is `Hom` in all modules after the full inclusion, so no
quasi-coherence of `𝒢` is asked for. This is not a restatement of the displayed equality: the
colimit is the one of `QCoh(𝒪_𝒳)`, and the source's argument is the one used here, that the
inclusion of `QCoh(𝒪_𝒳)` preserves colimits by the colimit clause of **Stacks 06WV (4)**,
`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion'`. -/
@[stacks 0GQZ "the 'in particular' clause: filtered colimits in QCoh(𝒪_𝒳)"]
theorem isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (G : _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hG : G.IsFinitePresentationOnSite)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    letI := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
    IsIso (colimit.post D ((_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι ⋙ coyoneda.obj (Opposite.op G))) :=
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have _ : PreservesColimitsOfSize.{u, u}
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι :=
    FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
  have _ := preservesColimitsOfShape_coyoneda_of_isQuasiCompactStack B S hS 𝒳 hqc h𝒳 G hG K
  inferInstance

/-- **Stacks 0GQZ in full.** For a quasi-compact and quasi-separated algebraic stack `𝒳`
(Stacks 04YB, Stacks 050D part (8)) and every small filtered index category `K`: for every
`𝒪_𝒳`-module `𝒢` of finite presentation (Stacks 03DL (7)), the displayed equality
`colim_i Hom_𝒳(𝒢, ℱ_i) = Hom_𝒳(𝒢, colim_i ℱ_i)` holds for every system `i ↦ ℱ_i` of `𝒪_𝒳`-modules
indexed by `K`, *and* `Hom_𝒳(𝒢, -)` commutes with colimits of shape `K` taken in `QCoh(𝒪_𝒳)`.

The two conjuncts are
`AlgebraicGeometry.Stack.isIso_colimit_post_hom_of_isQuasiCompactStack` and
`AlgebraicGeometry.Stack.isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack`; the
colimits involved exist in both module categories. -/
@[stacks 0GQZ "the whole statement: the displayed colimit equality together with the 'in \
particular' clause for QCoh(𝒪_𝒳)"]
theorem isIso_colimit_post_hom_and_quasicoherent_of_isQuasiCompactStack
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (K : Type u) [Category.{u} K] [IsFiltered K] :
    ∀ (G : _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)),
      G.IsFinitePresentationOnSite →
        (∀ (D : K ⥤ _root_.SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS
            𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)),
          letI := FibredSite.hasColimitsOfShape_sheafOfModules_ringStructureSheafCore B S hS
            𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf K
          IsIso (colimit.post D (coyoneda.obj (Opposite.op G)))) ∧
        ∀ (D : K ⥤ FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids),
          letI := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids
          IsIso (colimit.post D ((_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
              .fppf)).ι ⋙ coyoneda.obj (Opposite.op G))) :=
  fun G hG =>
    ⟨fun D => isIso_colimit_post_hom_of_isQuasiCompactStack B S hS 𝒳 hqc h𝒳 G hG D,
      fun D => isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack B S hS 𝒳 hqc h𝒳 G hG D⟩

end QuasiCompactQuasiSeparated

end AlgebraicGeometry.Stack

end
