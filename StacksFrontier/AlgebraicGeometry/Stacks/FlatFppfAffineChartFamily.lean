module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleAffineChartReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# Stacks 07B3 (2): flat, locally finitely presented affine charts over which a module is presented

Let `H` be a quasi-coherent module on the flat-fppf site of an algebraic stack `𝒳` and `x₀` a
flat object over the scheme `U₀`. The proof of Stacks 07B3 takes an fppf covering of `x₀` over
whose members `H` has a global presentation (Stacks 03DL (6)), refines it by affine schemes, and
applies Stacks 07AQ (2) to the resulting family. This file produces the family: every point of
`U₀` is in the image of an arrow `y ⟶ x₀`, flat and locally of finite presentation on the
underlying schemes, from a flat object `y` over an affine scheme admitting an arrow to an object
over which `H` has a global presentation.

## Main results

* `AlgebraicGeometry.Stack.exists_mem_range_of_mem_associatedTopology_fppf`: a covering sieve of
  the fppf site of a category fibred in groupoids covers the points of the underlying scheme by
  arrows that are flat and locally of finite presentation on the underlying schemes.
* `AlgebraicGeometry.Stack.FlatFppf.exists_flat_lfp_affine_presented`: the family.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v v' w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of the fppf site of a category fibred in groupoids covers the points of the
underlying scheme by flat, locally finitely presented arrows.** Every point of the scheme under
`x` is in the image of the scheme under the source of some arrow of the sieve whose underlying
morphism of schemes is flat and locally of finite presentation. -/
theorem exists_mem_range_of_mem_associatedTopology_fppf {X : Type v} [Category.{v'} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x : X} {T : Sieve x}
    (hT : T ∈ associatedTopology B S hS p B.topology x)
    (t : (BigFppfOver.toScheme B S hS).obj (p.obj x)) :
    ∃ (z : X) (g : z ⟶ x), T g ∧
      Flat ((BigFppfOver.toScheme B S hS).map (p.map g)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (p.map g)) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p.map g)) := by
  obtain ⟨E, hE, hle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS p
    B.topology
    (fun F => (∀ i, Flat ((BigFppfOver.toScheme B S hS).map (F.2.f i)) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (F.2.f i))) ∧
      ∀ t : (BigFppfOver.toScheme B S hS).obj F.1, ∃ i,
        t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (F.2.f i)))
    (fun U R hR => by
      obtain ⟨I, W, m, hmR, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hR
      refine ⟨⟨I, fun i => Over.mk (m i ≫ U.hom), fun i => Over.homMk (m i)⟩,
        ⟨fun i => ⟨hflat i, hlfp i⟩, fun t => hsurj t⟩, ?_⟩
      rintro _ _ ⟨i⟩
      exact hmR i)
    hp T hT
  obtain ⟨i, hi⟩ := hE.2 t
  exact ⟨E.X i, E.f i, hle _ _ (Presieve.ofArrows.mk i), (hE.1 i).1, (hE.1 i).2, hi⟩

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] isContinuous_inclusion_topology

/-- **The flat, locally finitely presented affine charts of 07B3 (2).** Let `H` be a quasi-coherent
module on the flat-fppf site of `𝒳` and `x₀` a flat object. Every point of the scheme under `x₀`
is in the image of an arrow `g : y ⟶ x₀`, flat and locally of finite presentation on the
underlying schemes, from a flat object `y` over an affine scheme with an arrow to an object over
which `H` has a global presentation. -/
theorem exists_flat_lfp_affine_presented
    {R : Sheaf (topology B S hS 𝒳) RingCat.{u}} (H : SheafOfModules.{m} R)
    (hH : H.IsQuasicoherentOnSite) (x₀ : 𝒳.val.val.obj) (hx₀ : flatObject B S hS 𝒳.val x₀)
    (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀)) :
    ∃ (y V : FlatFppf B S hS 𝒳) (_ : y ⟶ V) (g : y.obj ⟶ x₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)) ∧
      (H.over V).HasGlobalPresentation ∧
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g)) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g)) := by
  let X₀ : FlatFppf B S hS 𝒳 := ⟨x₀, hx₀⟩
  obtain ⟨I, V, fV, hcov, hpres⟩ := hH.locally_hasGlobalPresentation X₀
  have hcov' := (CoverPreserving.of_isContinuous (objectProperty B S hS 𝒳).ι
    (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)).cover_preserve hcov
  obtain ⟨z, g, hg, hflat, hlfp, s, hs⟩ := exists_mem_range_of_mem_associatedTopology_fppf B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hcov' t
  obtain ⟨Z, k, l, hk, rfl⟩ := hg
  obtain ⟨i, m, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  obtain ⟨y', g', haff, hopen, s', hs'⟩ := exists_affine_hom_mem_range B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids z s
  have hopen' : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g')) := hopen
  let G := l ≫ (objectProperty B S hS 𝒳).ι.map (m ≫ fV i)
  obtain ⟨hflat', hlfp'⟩ : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g' ≫ G))) ∧
      LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g' ≫ G))) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨⟨y', flatObject_of_flat B S hS 𝒳 (g' ≫ G) hflat' hx₀⟩, V i,
    ObjectProperty.homMk (g' ≫ l ≫ m.hom), g' ≫ G, haff, hpres i,
    hflat', hlfp', s', ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hs', hs]

end FlatFppf

end AlgebraicGeometry.Stack
