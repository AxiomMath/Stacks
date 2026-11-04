module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSliceDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Reverse

/-!
# Equality of morphisms of a fibre is h local, from the conditions of Stacks 0EX9

Two morphisms of the fibre over an object `U` of the big h category over `S` which have the same
base change along every member of an h covering family of `U` are equal, as soon as the category
fibred in groupoids satisfies conditions (1), (2) and (3) of Stacks 0EX9. This is the
separatedness half of condition (2) of Stacks 02ZI, and it is the first of the two statements the
sufficiency direction of Stacks 0EX9 needs.

The proof is `AlgebraicGeometry.BigHOver.of_localOnGenerators` applied to the property

> the base changes of the two morphisms along `Y ⟶ U` agree

of an object `Y` of the slice at `U`, which is stable under precomposition by
`CategoryTheory.Functor.pullbackFiberHom_comp_base`.  Its four hypotheses are:

* Zariski-locality, which is the uniqueness half of
  `CategoryTheory.Functor.existsUnique_fiberHom_of_isStackInGroupoids` for condition (1);
* descent along a flat proper surjection of finite presentation onto an affine object and across
  the two generator almost blowup squares, which are *faithfulness* of the comparison functors of
  conditions (2) and (3), in the form `AlgebraicGeometry.BigHOver.eq_of_fiberPullback_map_eq`.

Two identifications are used silently and hold by `rfl`: the chosen pullback of an object of a
fibre is the value of the pullback functor
(`CategoryTheory.Functor.pullbackFiber p x f = (CategoryTheory.Functor.IsFibered.fiberPullback
f).obj x`), and likewise for morphisms, so the language of
`CategoryTheory.Functor.pullbackFiberHom` and the language of the comparison functors of this
chapter are the same.

The site-level cartesianness that conditions (2) and (3) quantify over is recovered from the
cartesianness of the underlying square of schemes by `CategoryTheory.IsPullback.of_map_of_faithful`
for the underlying-scheme functor, as in `AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`.

## Main results

* `AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering`: the statement above.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-- Equality of the base changes of two morphisms of a fibre passes to a refinement. -/
public theorem pullbackFiberHom_eq_of_fac {U A A' : BigHOver B S hS} {x y : p.Fiber U}
    (m m' : x ⟶ y) (b : A ⟶ U) (γ : A' ⟶ A) (b' : A' ⟶ U) (hγ : γ ≫ b = b')
    (h : Functor.pullbackFiberHom m b = Functor.pullbackFiberHom m' b) :
    Functor.pullbackFiberHom m b' = Functor.pullbackFiberHom m' b' := by
  subst hγ
  rw [Functor.pullbackFiberHom_comp_base, Functor.pullbackFiberHom_comp_base, h]

/-- Equality of the base changes of two morphisms of a fibre along a morphism factoring through
`b` is equality of the base changes, along the remaining factor, of their base changes along
`b`. -/
public theorem pullbackFiberHom_base_eq_of_fac {U A A' : BigHOver B S hS} {x y : p.Fiber U}
    (m m' : x ⟶ y) (b : A ⟶ U) (γ : A' ⟶ A) (b' : A' ⟶ U) (hγ : γ ≫ b = b')
    (h : Functor.pullbackFiberHom m b' = Functor.pullbackFiberHom m' b') :
    Functor.pullbackFiberHom (Functor.pullbackFiberHom m b) γ =
      Functor.pullbackFiberHom (Functor.pullbackFiberHom m' b) γ := by
  subst hγ
  rw [Functor.pullbackFiberHom_comp_base, Functor.pullbackFiberHom_comp_base] at h
  rw [cancel_epi, cancel_mono] at h
  exact h

/-- **Equality of morphisms of a fibre is h local.** Two morphisms of the fibre over `U` whose base
changes along every member of an h covering family of `U` agree are equal, for a category fibred in
groupoids over the big h category over `S` satisfying conditions (1), (2) and (3) of
Stacks 0EX9. -/
public theorem eq_of_pullbackFiberHom_eq_of_covering
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    {U : BigHOver B S hS} {x y : p.Fiber U} (m m' : x ⟶ y)
    {I : Type (u + 1)} {V : I → BigHOver B S hS} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    (hm : ∀ i, Functor.pullbackFiberHom m (f i) = Functor.pullbackFiberHom m' (f i)) :
    m = m' := by
  classical
  refine Functor.eq_of_pullbackFiberHom_eq m m' (𝟙 U) ?_
  refine of_localOnGenerators B S hS U
    (fun Y ↦ Functor.pullbackFiberHom m Y.hom = Functor.pullbackFiberHom m' Y.hom)
    (fun k hY ↦ pullbackFiberHom_eq_of_fac m m' _ k.left _ (Over.w k) hY) ?_ ?_ ?_ ?_ f hf hm
  · -- Zariski: the uniqueness half of condition (1)
    intro Y E hE hEi
    have hcov : Sieve.ofArrows (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left) ∈
        zariskiTopology B S hS Y.left :=
      Precoverage.generate_mem_toGrothendieck
        ⟨⟨E.I₀, fun i ↦ (E.X i).left, fun i ↦ (E.f i).left⟩, rfl, hE⟩
    have key := Functor.existsUnique_fiberHom_of_isStackInGroupoids h1
      (fun i ↦ (E.f i).left) hcov
      (fun i ↦ Functor.pullbackFiberHom (Functor.pullbackFiberHom m Y.hom) ((E.f i).left))
      (fun i j Z ε ε' q h₁ h₂ ↦ Functor.baseChangeFiberMor_hom_eq
        (((Functor.IsFibered.pullbackPseudofunctor p).toDescentData
          (fun i ↦ (E.f i).left)).map (Functor.pullbackFiberHom m Y.hom)) ε ε' h₁ h₂)
    refine key.unique (fun i ↦ rfl) (fun i ↦ ?_)
    exact (pullbackFiberHom_base_eq_of_fac m m' Y.hom ((E.f i).left) (E.X i).hom
      (Over.w (E.f i)) (hEi i)).symm
  · -- a flat proper surjection of finite presentation onto an affine object: faithfulness of the
    -- descent-data functor of condition (2)
    intro Y Y' g hAff hflat hproper hsurj hfp hY'
    have hstep := pullbackFiberHom_base_eq_of_fac m m' Y.hom g.left Y'.hom (Over.w g) hY'
    have := h2 Y.left Y'.left g.left hAff hflat hproper hsurj hfp
    refine ((Functor.IsFibered.pullbackPseudofunctor p).toDescentData
      (fun _ : PUnit.{u + 2} ↦ g.left)).map_injective
      (Pseudofunctor.DescentData.hom_ext fun _ ↦ ?_)
    exact (Functor.pullbackPseudofunctor_map_map p g.left _).trans
      (hstep.trans (Functor.pullbackPseudofunctor_map_map p g.left _).symm)
  all_goals
    -- the squares of Examples 0EVG and 0EVH: faithfulness of the comparison functor of
    -- condition (3), respectively its two generator variant
    intro X X' Z E b z q e Id hAff hb hZ hsq hmod hZΨ hX'Ψ
    have hsq' : IsPullback e.left q.left z.left b.left :=
      IsPullback.of_map_of_faithful (BigHOver.toScheme B S hS) hsq
    refine eq_of_fiberPullback_map_eq b.left z.left q.left e.left hsq' ?_
      _ _ (pullbackFiberHom_base_eq_of_fac m m' X.hom z.left Z.hom (Over.w z) hZΨ)
      (pullbackFiberHom_base_eq_of_fac m m' X.hom b.left X'.hom (Over.w b) hX'Ψ)
    first
      | exact h3 _ _ _ _ _ _ _ _ Id hAff hb hZ hsq' hsq hmod
      | exact h4 _ _ _ _ _ _ _ _ Id hAff hb hZ hsq' hsq hmod

end BigHOver

end AlgebraicGeometry

end
