module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyAtlasCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatRefinement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# The flat objects of an algebraic stack cover its site

Let `𝒳` be an algebraic stack.  A smooth surjective 1-morphism `a : (Sch/U) ⟶ 𝒳`
(**Stacks 04T5**) names a flat object `x = a(1_U)` (**Stacks 0787**), and every object of the
fppf site of `𝒳` is covered by objects admitting a morphism to `x`: the fibre lifts of `a` along
an fppf covering (**Stacks 06QA**) are such objects.  So the family of flat objects covers the
final object of the site.

Combined with the refinement of covering sieves of a flat object by coverings with flat sources
(`AlgebraicGeometry.Stack.exists_flatObject_covering_le_of_mem_associatedTopology`), this gives:
for every property `P` of objects which is local in the sense that each flat object is covered by
flat objects satisfying `P`, the flat objects satisfying `P` cover the site.  It is how the
quasi-coherence of a module on `𝒳` is read on the flat objects alone.

## Main results

* `AlgebraicGeometry.Stack.exists_flatObject_cover_nonempty_hom`: every object is covered by
  objects admitting a morphism to one fixed flat object.
* `AlgebraicGeometry.Stack.coversTop_flatObject_of_local`: the flat objects with a local property
  cover the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Every object of the fppf site of an algebraic stack is covered by objects admitting a
morphism to one fixed flat object**: the image of the terminal object under a smooth surjective
1-morphism from a scheme, whose fibre lifts along fppf coverings (**Stacks 06QA**) give the
covering. -/
theorem exists_flatObject_cover_nonempty_hom :
    ∃ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x ∧
      ∀ z : 𝒳.val.val.obj, ∃ T ∈ fppfTopology B S hS 𝒳.val z,
        ∀ ⦃y : 𝒳.val.val.obj⦄ (g : y ⟶ z), T.arrows g → Nonempty (y ⟶ x) := by
  classical
  obtain ⟨U₀, f, hsm, hsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let F := CatFiberedInGroupoids.homFunctor f.hom
  refine ⟨F.obj (Over.mk (𝟙 U₀)), flatObject_of_smoothObject B S hS 𝒳
    (smoothObject_atlas_obj B S hS f hsm), fun z => ?_⟩
  obtain ⟨R, hR, hlift⟩ := exists_fppfCovering_fibre_lift B S hS f hsurj
    (AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm)
    (𝒳.val.val.p.obj z) (Functor.Fiber.mk (a := z) rfl)
  have hch : ∀ i : Σ V : BigFppfOver B S hS, {k : V ⟶ 𝒳.val.val.p.obj z // R.arrows k},
      ∃ (a : (schemeStack.{u, w} B S hS U₀).val.val.obj) (φ : F.obj a ⟶ z),
        𝒳.val.val.p.IsHomLift i.2.1 φ := fun i => hlift i.2.2
  choose a φ hφ using hch
  refine ⟨Sieve.ofArrows (fun i => F.obj (a i)) φ, ?_, ?_⟩
  · rw [fppfTopology, associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.val.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    refine (B.topology.over (B.obj hS)).superset_covering ?_ hR
    intro V k hk
    let i : Σ V' : BigFppfOver B S hS, {k' : V' ⟶ 𝒳.val.val.p.obj z // R.arrows k'} :=
      ⟨V, k, hk⟩
    have hinst := hφ i
    have hdom : 𝒳.val.val.p.obj (F.obj (a i)) = V :=
      IsHomLift.domain_eq 𝒳.val.val.p k (φ i)
    have hfac : 𝒳.val.val.p.map (φ i) = eqToHom hdom ≫ k := by
      simpa using IsHomLift.fac' 𝒳.val.val.p k (φ i)
    refine ⟨𝒳.val.val.p.obj (F.obj (a i)), eqToHom hdom.symm, 𝒳.val.val.p.map (φ i),
      Presieve.ofArrows.mk i, ?_⟩
    rw [hfac, eqToHom_trans_assoc]
    simp
  · intro y g hg
    obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff (fun i => F.obj (a i)) φ g).1 hg
    exact ⟨c ≫ F.map (Over.homMk (a i).hom (Category.comp_id (a i).hom))⟩

/-- **The flat objects with a local property cover the site.**  Let `P` be a property of objects
such that every flat object is covered by flat objects with `P`.  Then the flat objects with `P`
cover the final object of the fppf site of `𝒳`. -/
theorem coversTop_flatObject_of_local (P : 𝒳.val.val.obj → Prop)
    (hP : ∀ x, flatObject B S hS 𝒳.val x →
      Sieve.ofObjects (fun z : {z // flatObject B S hS 𝒳.val z ∧ P z} => z.1) x ∈
        fppfTopology B S hS 𝒳.val x) :
    (fppfTopology B S hS 𝒳.val).CoversTop
      (fun z : {z // flatObject B S hS 𝒳.val z ∧ P z} => z.1) := by
  obtain ⟨x, hx, hcov⟩ := exists_flatObject_cover_nonempty_hom B S hS 𝒳
  intro U
  obtain ⟨T, hT, hT'⟩ := hcov U
  refine (fppfTopology B S hS 𝒳.val).transitive hT _ fun y g hg => ?_
  obtain ⟨h⟩ := hT' g hg
  refine (fppfTopology B S hS 𝒳.val).superset_covering ?_
    ((fppfTopology B S hS 𝒳.val).pullback_stable h (hP x hx))
  exact fun _ _ hk => hk

section Quasicoherent

variable {R : Sheaf (fppfTopology B S hS 𝒳.val) RingCat.{u}}

/-- A covering sieve of a flat object contains a covering family of flat objects over each of
which a quasi-coherent module has a global presentation. -/
theorem exists_flatObject_covering_hasGlobalPresentation (M : SheafOfModules.{u + 1} R)
    (hM : M.IsQuasicoherentOnSite) {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x) :
    ∃ E : PreZeroHypercover.{u + 1} x,
      (∀ i, flatObject B S hS 𝒳.val (E.X i) ∧ (M.over (E.X i)).HasGlobalPresentation) ∧
        Sieve.generate E.presieve₀ ∈ fppfTopology B S hS 𝒳.val x := by
  obtain ⟨I, V, f, hcov, hpres⟩ := hM.locally_hasGlobalPresentation x
  obtain ⟨E, hflat, hE, hle⟩ := exists_flatObject_covering_le_of_mem_associatedTopology
    B S hS 𝒳 (τ := .fppf) hx (Sieve.ofArrows V f) hcov
  refine ⟨E, fun j => ⟨hflat j, ?_⟩, hE⟩
  obtain ⟨Y, h, _, ⟨i⟩, _⟩ := hle _ _ (Presieve.ofArrows.mk j)
  exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M h (hpres i)

/-- **The flat objects over which two quasi-coherent modules both have a global presentation
cover the site.** -/
theorem coversTop_flatObject_hasGlobalPresentation (M N : SheafOfModules.{u + 1} R)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (fppfTopology B S hS 𝒳.val).CoversTop
      (fun z : {z // flatObject B S hS 𝒳.val z ∧
        ((M.over z).HasGlobalPresentation ∧ (N.over z).HasGlobalPresentation)} => z.1) := by
  refine coversTop_flatObject_of_local B S hS 𝒳 _ fun x hx => ?_
  obtain ⟨E, hE, hcov⟩ := exists_flatObject_covering_hasGlobalPresentation B S hS 𝒳 M hM hx
  refine (fppfTopology B S hS 𝒳.val).transitive hcov _ fun W g hg => ?_
  obtain ⟨Y, h, k, ⟨j⟩, rfl⟩ := hg
  obtain ⟨E', hE', hcov'⟩ :=
    exists_flatObject_covering_hasGlobalPresentation B S hS 𝒳 N hN (hE j).1
  refine (fppfTopology B S hS 𝒳.val).superset_covering ?_
    ((fppfTopology B S hS 𝒳.val).pullback_stable h hcov')
  rintro W' m ⟨Y', a, b, ⟨l⟩, hab⟩
  refine (Sieve.mem_ofObjects_iff _ _).2 ⟨⟨E'.X l, (hE' l).1,
    Stacks.SheafOfModules.hasGlobalPresentation_overMap M (E'.f l) (hE j).2, (hE' l).2⟩,
    ⟨a⟩⟩

end Quasicoherent

end AlgebraicGeometry.Stack
