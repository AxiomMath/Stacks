module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ChartDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AtlasPairFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreProducts
import all StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations

/-!
# Flat factorization of two arrows into a chart of an algebraic stack

Let `c` be a chart of an algebraic stack `𝒳`: a scheme `U` and a smooth surjective 1-morphism
`f : (Sch/U) ⟶ 𝒳`. Let `z, z'` be objects of `Sch/U` flat over `U`, and let `y` be an object of
`𝒳` with arrows `ψ : y ⟶ f z` and `ψ' : y ⟶ f z'`. Then, fppf-locally on `y`, the pair
`(ψ, ψ')` factors through the image `f z''` of an object `z''` of `Sch/U` lying over an affine
scheme and flat over `U`, by arrows `f z'' ⟶ f z` and `f z'' ⟶ f z'` lying over flat morphisms
of schemes (`AlgebraicGeometry.Stack.AlgebraicStacks.Chart.exists_flat_factorization`). For
the chart affines of `AlgebraicGeometry.Stack.AlgebraicStacks.Chart.IsChartAffine` this is
`AlgebraicGeometry.Stack.AlgebraicStacks.Chart.flatChartFactorization`.

This is the property of the arrow space `U ×_𝒳 U` of the chart that the descent of modules along
the chart uses (step (C) of the construction of a separator for `QCoh(𝒪_𝒳)` in Stacks 0778).
The flatness of `z` and `z'` over `U` cannot be dropped: for `𝒳 = U = Spec k[s,t]` with the
identity chart, `z = V(s)`, `z' = V(t)` and `y` the origin, every `z''` mapping to both is killed
by `s` and `t`, hence is not flat over `z`.

## Proof

The two arrows give `γ = ψ ≫ f(z → U)` and `γ' = ψ' ≫ f(z' → U)` into `A₀ = f(𝟙_U)`, and by
`AlgebraicGeometry.Stack.exists_atlasPair_factorization` (the 2-fibre product `U ×_𝒳 U` is
smooth over each factor) they factor locally through an object `E` with two arrows
`β₁, β₂ : E ⟶ A₀` lying over smooth morphisms. Pull `E` back along `f z ⟶ A₀` (via `β₁`) and
along `f z' ⟶ A₀` (via `β₂`): in a category fibred in groupoids these pullbacks exist and lie
over pullbacks of schemes (**Stacks 06N5**), and all their projections lie over flat morphisms,
the arrows `f z ⟶ A₀`, `f z' ⟶ A₀` lying over the flat structure morphisms of `z`, `z'`. The
arrow from `y` lands in the pullback. Covering the pullback by affine objects and identifying
each with the image of an object of `Sch/U` by the cartesian factorization over `U` gives `z''`.

## References

* [Stacks Project, Tag 06N5](https://stacks.math.columbia.edu/tag/06N5)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- An arrow of an algebraic stack lying over a flat morphism of the base lies over a flat
morphism of schemes. -/
theorem flat_toScheme_map_of_isHomLift {U V : BigFppfOver B S hS} {x y : 𝒳.val.val.obj}
    (k : U ⟶ V) (α : x ⟶ y) (hα : 𝒳.val.val.p.IsHomLift k α)
    (hk : Flat ((BigFppfOver.toScheme B S hS).map k)) :
    Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) := by
  have := hα
  rw [IsHomLift.fac' 𝒳.val.val.p k α]
  simp only [Functor.map_comp]
  infer_instance

/-- The pullback of two arrows of an algebraic stack exists and its image in schemes is a
pullback square. -/
private theorem exists_isPullback_toScheme_map {x y z : 𝒳.val.val.obj} (φ : x ⟶ y) (g : z ⟶ y) :
    ∃ _ : HasPullback φ g, IsPullback
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (pullback.fst φ g)))
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (pullback.snd φ g)))
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ))
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g)) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map φ) φ :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have : HasPullback φ g := Functor.IsFibered.hasPullback_of_isStronglyCartesian 𝒳.val.val.p φ g
  exact ⟨this, (Functor.IsFibered.map_isPullback_of_isStronglyCartesian 𝒳.val.val.p φ g).map
    (BigFppfOver.toScheme B S hS)⟩

/-- **Flat base change in an algebraic stack.** The pullback of an arrow `g` lying over a flat
morphism of schemes, along any arrow `φ`, exists and its first projection lies over a flat
morphism of schemes: the structure functor carries the pullback square to a pullback square,
Stacks 06N5, and so does the passage to schemes. -/
theorem flat_map_pullback_fst {x y z : 𝒳.val.val.obj} (φ : x ⟶ y) (g : z ⟶ y)
    (hg : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g))) :
    ∃ _ : HasPullback φ g,
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (pullback.fst φ g))) := by
  obtain ⟨hp, h⟩ := exists_isPullback_toScheme_map (𝒳 := 𝒳) φ g
  exact ⟨hp, MorphismProperty.of_isPullback (P := @Flat) h.flip hg⟩

/-- The pullback of an arrow lying over a flat morphism of schemes has its second projection
lying over a flat morphism of schemes. -/
theorem flat_map_pullback_snd {x y z : 𝒳.val.val.obj} (φ : x ⟶ y) (g : z ⟶ y)
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ))) :
    ∃ _ : HasPullback φ g,
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (pullback.snd φ g))) := by
  obtain ⟨hp, h⟩ := exists_isPullback_toScheme_map (𝒳 := 𝒳) φ g
  exact ⟨hp, MorphismProperty.of_isPullback (P := @Flat) h hφ⟩

namespace Chart

variable (c : Chart 𝒳)

/-- The chart as a 1-morphism of algebraic stacks out of the algebraic stack of its scheme. -/
abbrev toStack : schemeStack.{u, w} B S hS c.U ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom c.f

/-- The chart is a smooth 1-morphism of algebraic stacks. -/
theorem isSmooth_toStack : AlgebraicStacks.IsSmooth B S hS c.toStack :=
  hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ c.isRepresentable
    (fun V y hy G hG he => (c.surjective_smooth V y hy G hG he).2)

/-- **Flat factorization through a chart.** Two arrows `ψ : y ⟶ f z`, `ψ' : y ⟶ f z'` into the
images of objects of `Sch/U` flat over `U` factor, fppf-locally on `y`, through the image of an
object of `Sch/U` lying over an affine scheme and flat over `U`, by arrows lying over flat
morphisms of schemes. -/
theorem exists_flat_factorization (y : 𝒳.val.val.obj)
    (z z' : (schemeFibredCategory B S hS c.U).val.obj)
    (hz : Flat ((BigFppfOver.toScheme B S hS).map z.hom))
    (hz' : Flat ((BigFppfOver.toScheme B S hS).map z'.hom))
    (ψ : y ⟶ c.functor.obj z) (ψ' : y ⟶ c.functor.obj z') :
    ∃ R ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y,
      ∀ ⦃y'' : 𝒳.val.val.obj⦄ ⦃k : y'' ⟶ y⦄, R.arrows k →
        ∃ (z'' : (schemeFibredCategory B S hS c.U).val.obj)
          (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj z''.left))
          (_ : Flat ((BigFppfOver.toScheme B S hS).map z''.hom))
          (α : c.functor.obj z'' ⟶ c.functor.obj z)
          (α' : c.functor.obj z'' ⟶ c.functor.obj z') (β : y'' ⟶ c.functor.obj z''),
          β ≫ α = k ≫ ψ ∧ β ≫ α' = k ≫ ψ' ∧
            Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) ∧
            Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α')) := by
  let A₀ := c.functor.obj (Over.mk (𝟙 c.U))
  let τ (t : Over c.U) : c.functor.obj t ⟶ A₀ := c.functor.map (toUnit B S hS t)
  have hτ : ∀ t : Over c.U, Flat ((BigFppfOver.toScheme B S hS).map t.hom) →
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (τ t))) := fun t ht =>
    flat_toScheme_map_of_isHomLift _ _
      (isHomLift_atlasFunctor_map B S hS c.toStack (toUnit B S hS t)) ht
  obtain ⟨R₁, hR₁, hfac⟩ := exists_atlasPair_factorization B S hS c.toStack .fppf
    (fun m hm hs => generate_singleton_mem_baseOverTopology_fppf B S hS m hm hs)
    c.isSmooth_toStack y (ψ ≫ τ z) (ψ' ≫ τ z')
  let R : Sieve y :=
    { arrows := fun y'' k =>
        ∃ (z'' : (schemeFibredCategory B S hS c.U).val.obj)
          (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj z''.left))
          (_ : Flat ((BigFppfOver.toScheme B S hS).map z''.hom))
          (α : c.functor.obj z'' ⟶ c.functor.obj z)
          (α' : c.functor.obj z'' ⟶ c.functor.obj z') (β : y'' ⟶ c.functor.obj z''),
          β ≫ α = k ≫ ψ ∧ β ≫ α' = k ≫ ψ' ∧
            Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) ∧
            Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α'))
      downward_closed := by
        rintro Y Z k ⟨z'', hz₁, hz₂, α, α', β, h₁, h₂, h₃, h₄⟩ g
        exact ⟨z'', hz₁, hz₂, α, α', g ≫ β, by rw [Category.assoc, h₁, Category.assoc],
          by rw [Category.assoc, h₂, Category.assoc], h₃, h₄⟩ }
  refine ⟨R, GrothendieckTopology.transitive _ hR₁ R ?_, fun _ _ hk => hk⟩
  intro T' h hh
  obtain ⟨E, δ, β₁, β₂, e₁, e₂, s₁, s₂⟩ := hfac hh
  obtain ⟨_, hf₁⟩ := flat_map_pullback_fst (τ z) β₁ inferInstance
  obtain ⟨_, hs₁⟩ := flat_map_pullback_snd (τ z) β₁ (hτ z hz)
  let μ : pullback (τ z) β₁ ⟶ A₀ := pullback.snd (τ z) β₁ ≫ β₂
  have hμ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map μ)) := by
    simp only [μ, Functor.map_comp]
    infer_instance
  obtain ⟨_, hf₂⟩ := flat_map_pullback_fst μ (τ z') (hτ z' hz')
  obtain ⟨_, hs₂⟩ := flat_map_pullback_snd μ (τ z') hμ
  let πz : pullback μ (τ z') ⟶ c.functor.obj z := pullback.fst μ (τ z') ≫ pullback.fst (τ z) β₁
  let πz' : pullback μ (τ z') ⟶ c.functor.obj z' := pullback.snd μ (τ z')
  have hπz : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map πz)) := by
    simp only [πz, Functor.map_comp]
    infer_instance
  let m₁ : T' ⟶ pullback (τ z) β₁ := pullback.lift (h ≫ ψ) δ (by
    rw [e₁, Category.assoc])
  let m : T' ⟶ pullback μ (τ z') := pullback.lift m₁ (h ≫ ψ') (by
    simp only [μ, m₁, pullback.lift_snd_assoc, e₂, Category.assoc])
  have hmz : m ≫ πz = h ≫ ψ := by
    simp only [m, m₁, πz]
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hmz' : m ≫ πz' = h ≫ ψ' := by
    simp only [m, πz']
    rw [pullback.lift_snd]
  obtain ⟨I, Q, g, hcov, haff, hgflat⟩ :=
    exists_isAffine_covering_of_object B S hS 𝒳.val (pullback μ (τ z'))
  refine GrothendieckTopology.superset_covering _ ?_
    (GrothendieckTopology.pullback_stable _ m hcov)
  rintro T'' k ⟨Q', a', b', ⟨i⟩, hab⟩
  have : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g i))) := hgflat i
  have := hπz
  have := hs₂
  have : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (τ z))) := hτ z hz
  let γQ : Q i ⟶ A₀ := g i ≫ πz ≫ τ z
  have hγQ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map γQ)) := by
    simp only [γQ, Functor.map_comp]
    infer_instance
  let κ := kappaIso B S hS c.toStack γQ
  refine ⟨objOf B S hS c.toStack γQ, haff i, ?_, κ.inv ≫ g i ≫ πz, κ.inv ≫ g i ≫ πz',
    a' ≫ κ.hom, ?_, ?_, ?_, ?_⟩
  · change Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map γQ ≫ eqToHom _))
    rw [Functor.map_comp, eqToHom_map]
    infer_instance
  · rw [Category.assoc, κ.hom_inv_id_assoc, reassoc_of% hab, hmz, Category.assoc]
  · rw [Category.assoc, κ.hom_inv_id_assoc, reassoc_of% hab, hmz', Category.assoc]
  · simp only [Functor.map_comp]
    infer_instance
  · simp only [πz', Functor.map_comp]
    infer_instance

/-- **Flat factorization through the chart** (step (C) of the separator of Stacks 0778): an
object over an affine scheme with arrows to the images of two chart affines factors,
fppf-locally, through the image of a third chart affine by arrows lying over flat morphisms. -/
theorem flatChartFactorization : c.FlatChartFactorization := by
  intro y _ z z' hz hz' ψ ψ'
  obtain ⟨R, hR, hfac⟩ := c.exists_flat_factorization y z z' hz.2 hz'.2 ψ ψ'
  refine ⟨R, hR, fun y'' k hk => ?_⟩
  obtain ⟨z'', h₁, h₂, α, α', β, e, e', f, f'⟩ := hfac hk
  exact ⟨z'', ⟨h₁, h₂⟩, α, α', β, e, e', f, f'⟩

end Chart

end AlgebraicGeometry.Stack.AlgebraicStacks

end
