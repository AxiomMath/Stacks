module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSystemBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSystemRestrictIndex

/-!
# The localisation of an inverse system of schemes at a scheme over one of its levels

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system over a directed set, `c` a cone over it with vertex
`X`, `i₀ ∈ I` and `b : B ⟶ X_{i₀}` a morphism of schemes. For `i ≥ i₀` the fibre products
`B ×_{X_{i₀}} X_i` form an inverse system over the indices above `i₀`, with the projections to the
`X_i` a morphism of inverse systems, and `B ×_{X_{i₀}} X` is a cone over it. If `c` is a limit cone
then so is that cone: `B ×_{X_{i₀}} X = lim_{i ≥ i₀} B ×_{X_{i₀}} X_i`.

In particular, for a scheme `U_{i₀}` étale over the level `S_{i₀}` of an inverse system `S_i` with
limit `S`, the scheme `U_{i₀} ×_{S_{i₀}} S` is the limit of the `U_{i₀} ×_{S_{i₀}} S_i`
[Stacks, Tag 0EYM].

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.localizedDiagram` — the inverse system
  `i ↦ B ×_{X_{i₀}} X_i` over the indices above `i₀`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.localizedProj` — the projections to the `X_i`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.localizedCone` — the cone with vertex
  `B ×_{X_{i₀}} X`.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isLimitLocalizedCone` — it is a limit cone.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 01YV](https://stacks.math.columbia.edu/tag/01YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
  {B : Scheme.{u}} (b : B ⟶ D.obj (op i₀))

/-- The transition from an index above `i₀` to `i₀`. -/
def geIndexToBase (j : (GeIndex i₀)ᵒᵖ) : (geIndexOpFunctor i₀).obj j ⟶ op i₀ :=
  (homOfLE j.unop.2).op

/-- The transitions to `i₀` commute with the transitions between indices above `i₀`. -/
theorem geIndexToBase_comp {j k : (GeIndex i₀)ᵒᵖ} (a : j ⟶ k) :
    (geIndexOpFunctor i₀).map a ≫ geIndexToBase i₀ k = geIndexToBase i₀ j :=
  Subsingleton.elim _ _

/-- **The localised inverse system** `i ↦ B ×_{X_{i₀}} X_i` over the indices above `i₀`. -/
abbrev localizedDiagram : (GeIndex i₀)ᵒᵖ ⥤ Scheme.{u} where
  obj j := pullback b (D.map (geIndexToBase i₀ j))
  map {j k} a := pullback.map _ _ _ _ (𝟙 B) (D.map ((geIndexOpFunctor i₀).map a)) (𝟙 _)
    (by simp) (by rw [Category.comp_id, ← D.map_comp, geIndexToBase_comp])
  map_id j := by ext <;> simp [pullback.map]
  map_comp _ _ := pullback.hom_ext (by simp [pullback.map])
    (by simp [pullback.map])

/-- The level `j` of the localised inverse system is `B ×_{X_{i₀}} X_j`. -/
theorem localizedDiagram_obj (j : (GeIndex i₀)ᵒᵖ) :
    (localizedDiagram D i₀ b).obj j = pullback b (D.map (geIndexToBase i₀ j)) := rfl

/-- The transitions of the localised inverse system commute with the projections to `B`. -/
@[reassoc (attr := simp)]
theorem localizedDiagram_map_fst {j k : (GeIndex i₀)ᵒᵖ} (a : j ⟶ k) :
    (localizedDiagram D i₀ b).map a ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [localizedDiagram, pullback.map]

/-- The transitions of the localised inverse system lie over the transitions of `D`. -/
@[reassoc (attr := simp)]
theorem localizedDiagram_map_snd {j k : (GeIndex i₀)ᵒᵖ} (a : j ⟶ k) :
    (localizedDiagram D i₀ b).map a ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ D.map ((geIndexOpFunctor i₀).map a) := by
  simp [localizedDiagram, pullback.map]

/-- The projections `B ×_{X_{i₀}} X_i ⟶ X_i`, a morphism of inverse systems. -/
abbrev localizedProj : localizedDiagram D i₀ b ⟶ geIndexOpFunctor i₀ ⋙ D where
  app _ := pullback.snd _ _
  naturality _ _ a := localizedDiagram_map_snd D i₀ b a

variable (c : Cone D)

/-- **The cone with vertex `B ×_{X_{i₀}} X`** over the localised inverse system. -/
abbrev localizedCone : Cone (localizedDiagram D i₀ b) where
  pt := pullback b (c.π.app (op i₀))
  π :=
    { app := fun j => pullback.map _ _ _ _ (𝟙 B) (c.π.app ((geIndexOpFunctor i₀).obj j)) (𝟙 _)
        (by simp) (by rw [Category.comp_id]; exact (c.w (geIndexToBase i₀ j)).symm)
      naturality := fun _ _ _ => pullback.hom_ext
        (by simp [localizedDiagram, pullback.map])
        (by simp [localizedDiagram, pullback.map]) }

/-- The projections of the localised cone commute with the projections to `B`. -/
@[reassoc (attr := simp)]
theorem localizedCone_π_fst (j : (GeIndex i₀)ᵒᵖ) :
    (localizedCone D i₀ b c).π.app j ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The projections of the localised cone lie over the projections of `c`. -/
@[reassoc (attr := simp)]
theorem localizedCone_π_snd (j : (GeIndex i₀)ᵒᵖ) :
    (localizedCone D i₀ b c).π.app j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ c.π.app ((geIndexOpFunctor i₀).obj j) :=
  pullback.lift_snd _ _ _

/-- The projection `B ×_{X_{i₀}} X ⟶ X`. -/
abbrev localizedLimitMap : (localizedCone D i₀ b c).pt ⟶ c.pt := pullback.snd _ _

/-- The projections of the localised cone, followed by the projections to the `X_j`, agree with
the projection `B ×_{X_{i₀}} X ⟶ X` followed by the projections of `c`. -/
theorem localizedCone_proj (j : (GeIndex i₀)ᵒᵖ) :
    conePi (localizedCone D i₀ b c) j ≫ (localizedProj D i₀ b).app j =
      localizedLimitMap D i₀ b c ≫ conePi (c.whisker (geIndexOpFunctor i₀)) j :=
  localizedCone_π_snd D i₀ b c j

/-- The index `i₀` itself, as an index above `i₀`. -/
abbrev geIndexBase : (GeIndex i₀)ᵒᵖ := op ⟨i₀, le_rfl⟩

/-- **`B ×_{X_{i₀}} X` is the limit of the `B ×_{X_{i₀}} X_i`** when `X` is the limit of the
`X_i`. -/
def isLimitLocalizedCone [IsDirected I (· ≤ ·)] (hc : IsLimit c) :
    IsLimit (localizedCone D i₀ b c) := by
  let hcJ := isLimit_whisker_geIndexOpFunctor i₀ hc
  have hfst : ∀ (s : Cone (localizedDiagram D i₀ b)) (j : (GeIndex i₀)ᵒᵖ),
      s.π.app j ≫ pullback.fst _ _ = s.π.app (geIndexBase i₀) ≫ pullback.fst _ _ := by
    intro s j
    obtain ⟨m, hjm, h₀m⟩ := directed_of (· ≤ ·) j.unop.1 i₀
    rw [← s.w (homOfLE (y := ⟨m, h₀m⟩) hjm).op,
      ← s.w (homOfLE (x := (geIndexBase i₀).unop) (y := ⟨m, h₀m⟩) h₀m).op, Category.assoc,
      Category.assoc, localizedDiagram_map_fst, localizedDiagram_map_fst]
  let sJ : ∀ s : Cone (localizedDiagram D i₀ b), Cone (geIndexOpFunctor i₀ ⋙ D) := fun s =>
    { pt := s.pt
      π :=
        { app := fun j => s.π.app j ≫ pullback.snd _ _
          naturality := fun _ _ a => by simp [← s.w a, pullback.map] } }
  refine
    { lift := fun s => pullback.lift (s.π.app (geIndexBase i₀) ≫ pullback.fst _ _)
        (hcJ.lift (sJ s)) ?_
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · rw [Category.assoc, pullback.condition, ← c.w (geIndexToBase i₀ (geIndexBase i₀)),
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) (hcJ.fac (sJ s) (geIndexBase i₀)).symm
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, localizedCone_π_fst, pullback.lift_fst, hfst s j]
    · rw [Category.assoc, localizedCone_π_snd, ← Category.assoc, pullback.lift_snd]
      exact hcJ.fac (sJ s) j
  · refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hm (geIndexBase i₀), Category.assoc, localizedCone_π_fst]
    · rw [pullback.lift_snd]
      refine hcJ.hom_ext fun j => ?_
      rw [hcJ.fac (sJ s) j]
      change _ = s.π.app j ≫ pullback.snd _ _
      rw [← hm j, Category.assoc, Category.assoc, localizedCone_π_snd]
      rfl

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
