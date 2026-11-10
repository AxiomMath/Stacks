module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# Affine objects cover the fppf site of a stack, and the flat-fppf site

Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme `S` contained
in a big fppf site `B`, with the fppf topology of Stacks 06TP on its total category. Every
object `x` of `𝒳` lies over a scheme `U`, and an affine open covering of `U` lifts cartesianly
to a covering family of `x` whose members lie over affine schemes. Its members lie over open
immersions, which are flat, so when `𝒳` is an algebraic stack and `x` is a *flat* object in the
sense of Stacks 0H14 the lifted objects are flat too, and the same family is a covering family
of the flat-fppf site of Stacks 0787.

Both statements are of the shape `CategoryTheory.GrothendieckTopology.IsCoveringFamily`, the
hypothesis of the vanishing criteria of `StacksFrontier.CategoryTheory.Sites.VanishingOnCovering`.

## Main results

* `AlgebraicGeometry.Stack.exists_isAffine_covering_of_object`: an object of the fppf site of a
  category fibred in groupoids over the big fppf category of `S` has a covering family whose
  members lie over affine schemes and over flat morphisms of schemes.
* `AlgebraicGeometry.Stack.isCoveringFamily_isAffine_fppfTopology`: the objects lying over
  affine schemes are a covering family of the fppf site.
* `AlgebraicGeometry.Stack.FlatFppf.isCoveringFamily_isAffine`: the flat objects lying over
  affine schemes are a covering family of the flat-fppf site of an algebraic stack.

## References

* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness of the underlying morphism of schemes of a morphism of the big fppf category over
`S` is unaffected by precomposition with the comparison isomorphism of an equality of objects. -/
lemma flat_left_eqToHom_comp {V V' X : BigFppfOver B S hS} (h : V = V')
    (m : V' ⟶ X) (hm : Flat (B.inclusion.map m.left)) :
    Flat (B.inclusion.map (eqToHom h ≫ m).left) := by
  subst h
  simpa using hm

section Fibred

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **An object of the fppf site of a category fibred in groupoids over the big fppf category of
`S` is covered by objects lying over affine schemes.** The covering family can moreover be
chosen to consist of morphisms lying over flat morphisms of schemes. -/
theorem exists_isAffine_covering_of_object (x : 𝒳.val.obj) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳.val.obj) (f : ∀ i, y i ⟶ x),
      Sieve.generate (Presieve.ofArrows y f) ∈ fppfTopology B S hS 𝒳 x ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj (y i)))) ∧
      ∀ i, Flat (B.inclusion.map (𝒳.val.p.map (f i)).left) := by
  classical
  have hfib := 𝒳.isFiberedInGroupoids.isFibered
  set X : BigFppfOver B S hS := 𝒳.val.p.obj x
  let T : B.Schemes := X.left
  let U := (B.inclusion.obj T).affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  have hpre : W.presieve₀ ∈ B.precoverage T := ⟨W, rfl, hW⟩
  have hWaff : ∀ j, IsAffine (B.inclusion.obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom this
  have hWflat : ∀ j, Flat (B.inclusion.map (W.f j)) := fun j =>
    (flat_and_locallyOfFinitePresentation_of_mem_precoverage B _ hpre _
      (Presieve.ofArrows.mk j)).1
  let Vobj (j : W.I₀) : BigFppfOver B S hS := Over.mk (W.f j ≫ X.hom)
  let vmap (j : W.I₀) : Vobj j ⟶ X := Over.homMk (W.f j)
  let y (j : W.I₀) : 𝒳.val.obj :=
    Functor.IsPreFibered.pullbackObj (p := 𝒳.val.p) (a := x) rfl (vmap j)
  let g (j : W.I₀) : y j ⟶ x :=
    Functor.IsPreFibered.pullbackMap (p := 𝒳.val.p) (a := x) rfl (vmap j)
  have hproj : ∀ j, 𝒳.val.p.obj (y j) = Vobj j := fun j =>
    Functor.IsPreFibered.pullbackObj_proj (p := 𝒳.val.p) (a := x) rfl (vmap j)
  have hfac : ∀ j, 𝒳.val.p.map (g j) = eqToHom (hproj j) ≫ vmap j := by
    intro j
    simpa using IsHomLift.fac' 𝒳.val.p (vmap j) (g j)
  refine ⟨W.I₀, y, g, ?_, fun j => (hproj j) ▸ hWaff j, ?_⟩
  · rw [fppfTopology, associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows Vobj vmap ∈ BigFppfOver.topology B S hS X := by
      rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      change Sieve.ofArrows W.X W.f ∈ B.topology T
      simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hBcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    exact ⟨𝒳.val.p.obj (y j), eqToHom (hproj j).symm, 𝒳.val.p.map (g j),
      Presieve.ofArrows.mk j, by rw [hfac j]; simp⟩
  · intro j
    rw [hfac j]
    exact flat_left_eqToHom_comp B S hS (hproj j) (vmap j) (hWflat j)

/-- **The objects lying over affine schemes are a covering family of the fppf site of a category
fibred in groupoids over the big fppf category of `S`.** -/
theorem isCoveringFamily_isAffine_fppfTopology :
    (fppfTopology B S hS 𝒳).IsCoveringFamily
      (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj x))) := by
  intro x
  obtain ⟨I, y, f, hcov, haff, -⟩ := exists_isAffine_covering_of_object B S hS 𝒳 x
  exact ⟨Presieve.ofArrows y f, hcov, by rintro _ _ ⟨j⟩; exact haff j⟩

end Fibred

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The flat objects lying over affine schemes are a covering family of the flat-fppf site of
an algebraic stack.** -/
theorem isCoveringFamily_isAffine :
    (topology B S hS 𝒳).IsCoveringFamily
      (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x.obj))) := by
  intro x
  obtain ⟨I, y, f, hcov, haff, hflat⟩ :=
    exists_isAffine_covering_of_object B S hS 𝒳.val x.obj
  have hflatObj : ∀ i, flatObject B S hS 𝒳.val (y i) := fun i =>
    flatObject_of_flat B S hS 𝒳 (f i) (hflat i) x.property
  let yh (i : I) : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳) :=
    ⟨y i, hflatObj i⟩
  let fh (i : I) : yh i ⟶ x := ObjectProperty.homMk (f i)
  refine ⟨Presieve.ofArrows yh fh, ?_, by rintro _ _ ⟨j⟩; exact haff j⟩
  rw [← inclusionTopology_eq_topology B S hS 𝒳, inclusionTopology,
    Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck ⟨fun _ _ _ => inferInstance, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
  exact hcov

end FlatFppf

end AlgebraicGeometry.Stack

end
