module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected

/-!
# Closed subsets of the stages of a limit of Noetherian affine schemes

Let `V = lim Vᵢ` be a cofiltered limit of affine locally Noetherian schemes over `S`, as in the
limit preservation of Stacks 0GI5. This file records the first step of the injectivity half of
its proof ("agreement of `Z_{λ, i}`"): two closed subsets of `|Vᵢ|` with the same inverse image in
`|V|` have the same inverse image at a later stage, by Stacks 01Z4 applied to their quasi-compact
complements.

## Main results

* `AlgebraicGeometry.Artin.pointsMap_yoneda_preimage_eq`: inverse images of sets of points of a
  represented presheaf are inverse images of sets of scheme points.
* `AlgebraicGeometry.Artin.exists_preimage_eq_of_isClosed`: the agreement at a later stage.
* `CategoryTheory.Limits.isLimitMapOverBaseChangeCone`: the base change of a cofiltered limit
  along a morphism into a stage is again a limit, after any functor preserving fibre products.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image of a set of points of a represented presheaf along a morphism of the site
is the inverse image, along the underlying morphism of schemes, of the corresponding set of
scheme points. -/
theorem pointsMap_yoneda_preimage_eq {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (Z : Set (Space.points B S hS (yoneda.obj V))) :
    Space.pointsMap B S hS (yoneda.obj U) (yoneda.map g) ⁻¹' Z =
      Space.schemePointsHomeomorph B S hS U ⁻¹'
        ((BigFppfOver.toScheme B S hS).map g ⁻¹'
          ((Space.schemePointsHomeomorph B S hS V).symm ⁻¹' Z)) := by
  ext x
  simp only [Set.mem_preimage]
  rw [← Space.schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply]

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {c : Cone D}

/-- **Two closed subsets of a stage with the same inverse image in the limit agree at a later
stage.** For a cofiltered limit `V = lim Vᵢ` of affine locally Noetherian schemes over `S`, two
closed subsets of `|Vᵢ|` whose inverse images in `|V|` agree have the same inverse image in `|Vⱼ|`
for some `j ⟶ i`. The complements are quasi-compact opens of the Noetherian scheme `Vᵢ`, so this
is Stacks 01Z4 (2). -/
theorem exists_preimage_eq_of_isClosed
    (hc : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) (i : I)
    {Z₁ Z₂ : Set (Space.points B S hS (yoneda.obj (D.obj i).obj))}
    (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : Space.pointsMap B S hS (yoneda.obj c.pt.obj) (yoneda.map (c.π.app i).hom) ⁻¹' Z₁ =
      Space.pointsMap B S hS (yoneda.obj c.pt.obj) (yoneda.map (c.π.app i).hom) ⁻¹' Z₂) :
    ∃ (j : I) (f : j ⟶ i),
      Space.pointsMap B S hS (yoneda.obj (D.obj j).obj) (yoneda.map (D.map f).hom) ⁻¹' Z₁ =
        Space.pointsMap B S hS (yoneda.obj (D.obj j).obj) (yoneda.map (D.map f).hom) ⁻¹' Z₂ := by
  let X := D ⋙ LocallyNoetherianOver.toScheme B S hS
  have : ∀ i, IsAffine (X.obj i) := hD
  have : IsLocallyNoetherian (X.obj i) := (D.obj i).property
  have : IsNoetherian (X.obj i) := {}
  let e := Space.schemePointsHomeomorph B S hS (D.obj i).obj
  let U₁ : (X.obj i).Opens := ⟨(e.symm ⁻¹' Z₁)ᶜ, (h₁.preimage e.symm.continuous).isOpen_compl⟩
  let U₂ : (X.obj i).Opens := ⟨(e.symm ⁻¹' Z₂)ᶜ, (h₂.preimage e.symm.continuous).isOpen_compl⟩
  have key : ∀ {W : LocallyNoetherianOver B S hS} (g : W ⟶ D.obj i),
      Space.pointsMap B S hS (yoneda.obj W.obj) (yoneda.map g.hom) ⁻¹' Z₁ =
        Space.pointsMap B S hS (yoneda.obj W.obj) (yoneda.map g.hom) ⁻¹' Z₂ ↔
      (LocallyNoetherianOver.toScheme B S hS).map g ⁻¹ᵁ U₁ =
        (LocallyNoetherianOver.toScheme B S hS).map g ⁻¹ᵁ U₂ := by
    intro W g
    rw [pointsMap_yoneda_preimage_eq, pointsMap_yoneda_preimage_eq,
      (Space.schemePointsHomeomorph B S hS W.obj).surjective.preimage_injective.eq_iff,
      TopologicalSpace.Opens.ext_iff]
    change _ ↔ (_ ⁻¹' (e.symm ⁻¹' Z₁)ᶜ : Set _) = _ ⁻¹' (e.symm ⁻¹' Z₂)ᶜ
    rw [Set.preimage_compl, Set.preimage_compl, compl_inj_iff]
    rfl
  obtain ⟨j, f, hf⟩ := exists_map_preimage_eq_map_preimage X
    ((LocallyNoetherianOver.toScheme B S hS).mapCone c) hc (i := i) (U := U₁) (V := U₂)
    (TopologicalSpace.NoetherianSpace.isCompact _)
    (TopologicalSpace.NoetherianSpace.isCompact _) ((key (c.π.app i)).mp h)
  exact ⟨j, f, (key (D.map f)).mpr hf⟩

end AlgebraicGeometry.Artin

namespace CategoryTheory.Limits

/-! ### Base change of a cofiltered limit along a morphism into a stage -/

section BaseChange

variable {C : Type*} [Category C] [HasPullbacks C] {J : Type*} [Category J] (E : J ⥤ C)
  (c : Cone E) (j : J) {N : C} (n : N ⟶ E.obj j)

/-- The base change `k ↦ E k ×_{E j} N` of the part of a diagram over `j` along `n : N ⟶ E j`. -/
noncomputable abbrev overBaseChangeDiagram : Over j ⥤ C where
  obj k := pullback (E.map k.hom) n
  map {k l} φ := pullback.lift (pullback.fst _ _ ≫ E.map φ.left) (pullback.snd _ _)
    (by rw [Category.assoc, ← E.map_comp, Over.w φ, pullback.condition])
  map_id k := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp
    · rw [pullback.lift_snd]
      simp
  map_comp φ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Over.comp_left, Functor.map_comp, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- The base change `X ×_{E j} N` of a cone, as a cone over `k ↦ E k ×_{E j} N`. -/
noncomputable abbrev overBaseChangeCone : Cone (overBaseChangeDiagram E j n) where
  pt := pullback (c.π.app j) n
  π :=
    { app := fun k => pullback.lift (pullback.fst _ _ ≫ c.π.app k.left) (pullback.snd _ _)
        (by rw [Category.assoc, c.w, pullback.condition])
      naturality := fun k l φ => by
        apply pullback.hom_ext
        · change (𝟙 _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ =
            (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
          rw [Category.id_comp, pullback.lift_fst, Category.assoc, pullback.lift_fst,
            pullback.lift_fst_assoc, Category.assoc, c.w]
        · change (𝟙 _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ =
            (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
          rw [Category.id_comp, pullback.lift_snd, Category.assoc, pullback.lift_snd,
            pullback.lift_snd] }

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- **The base change of a limit along a morphism into a stage is a limit**, after any functor
`L` preserving fibre products: if `L` carries a cone over a cofiltered diagram to a limit cone,
then it carries its base change along `n : N ⟶ E j` to a limit cone. -/
noncomputable def isLimitMapOverBaseChangeCone {D : Type*} [Category D] (L : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan L] [IsCofiltered J] (hc : IsLimit (L.mapCone c)) :
    IsLimit (L.mapCone (overBaseChangeCone E c j n)) := by
  let α : overBaseChangeDiagram E j n ⋙ L ⟶ Over.forget j ⋙ E ⋙ L :=
    { app := fun k => L.map (pullback.fst (E.map k.hom) n)
      naturality := fun k l φ => by
        change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
        rw [← L.map_comp, ← L.map_comp, pullback.lift_fst]
        rfl }
  let f : (Cone.postcompose α).obj (L.mapCone (overBaseChangeCone E c j n)) ⟶
      (L.mapCone c).whisker (Over.forget j) :=
    { hom := L.map (pullback.fst (c.π.app j) n)
      w := fun k => by
        change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
        rw [← L.map_comp, ← L.map_comp, pullback.lift_fst]
        rfl }
  refine isLimitOfIsPullbackOfIsConnected α _ _ f (fun k => ?_)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (L.mapCone c)).symm hc)
  have hsq : IsPullback ((overBaseChangeCone E c j n).π.app k) (pullback.fst (c.π.app j) n)
      (pullback.fst (E.map k.hom) n) (c.π.app k.left) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (E.map k.hom) n).flip
    rw [pullback.lift_snd]
    exact (c.w k.hom).symm ▸ (IsPullback.of_hasPullback (c.π.app j) n).flip
  exact hsq.map L

end BaseChange

end CategoryTheory.Limits

end
