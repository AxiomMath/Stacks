module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmoothRefinement

/-!
# Étale refinements of smooth coverings of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Every smooth covering of an algebraic
space over `S` (Stacks 041C) is refined by an étale covering of it (Stacks 041E). So the étale
coverings are cofinal among the smooth ones, and the smooth and étale topologies on the
algebraic spaces over `S` agree.

## Main results

* `AlgebraicGeometry.Space.exists_isEtaleCovering_refining_isSmoothCovering`: every smooth
  covering of an algebraic space is refined by an étale covering of it.

## References

* [Stacks Project, Tag 0CFV](https://stacks.math.columbia.edu/tag/0CFV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A smooth covering of an algebraic space over `S` is refined by an étale covering of it: there
is an étale covering each of whose members factors through a member of the given smooth covering,
compatibly with the morphisms to the common target. -/
@[stacks 0CFV]
theorem exists_isEtaleCovering_refining_isSmoothCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsSmoothCovering B S hS X f) :
    ∃ (J : Type u) (U : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ j, U j ⟶ F),
      IsEtaleCovering B S hS U g ∧
        ∀ j, ∃ (i : I) (h : U j ⟶ X i), h ≫ f i = g j := by
  classical
  let toSch := BigFppfOver.toScheme B S hS
  let FObj : AlgebraicSpaces B S hS := ⟨F, hf.target_isAlgebraicSpace⟩
  let XObj : I → AlgebraicSpaces B S hS := fun i => ⟨X i, hf.source_isAlgebraicSpace i⟩
  let fObj : ∀ i, XObj i ⟶ FObj := fun i => ObjectProperty.homMk (f i)
  have hcover : Topology.IsCovering .smooth B S hS
      (fun i => (XObj i).1) (fun i => (fObj i).hom) :=
    ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace, hf⟩
  obtain ⟨T₀, b, hbSurj, hbEtale⟩ := hf.target_isAlgebraicSpace.exists_atlas
  obtain ⟨Y, q, pr, hY, hpb⟩ :=
    isSmoothCovering_baseChange_of_chart B S hS XObj fObj hcover T₀ b
  choose W w hwSurj hwEtale using fun k => (Y k).property.exists_atlas
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, W p.1 ⟶ T₀ :=
    fun p => yoneda.preimage (w p.1 ≫ (q p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = w p.1 ≫ (q p.1).hom := by
    simp [d]
  have hspace := etale_atlases_comp_isSmoothCovering B S hS Y
    (representedAlgebraicSpace B S hS T₀) q hY W w hwSurj hwEtale
  have hspaceD : Topology.IsCovering .smooth B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (W p.1))
      (fun p => yoneda.map (d p)) := by
    simpa only [hd] using hspace
  let E : PreZeroHypercover.{v} (toSch.obj T₀) :=
    { I₀ := Σ _ : I, PUnit.{v + 1}
      X := fun p => toSch.obj (W p.1)
      f := fun p => toSch.map (d p) }
  have hE : E.presieve₀ ∈ Scheme.precoverage (@Smooth.{u}) (toSch.obj T₀) :=
    isSmoothCovering_yoneda_of_isCovering B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => W p.1) T₀ d hspaceD
  let 𝒰 : (toSch.obj T₀).Cover.{v} (Scheme.precoverage (@Smooth.{u})) :=
    { toPreZeroHypercover := E, mem₀ := hE }
  obtain ⟨J, A, p, hAff, hEt, hAsurj, hArefine⟩ :=
    exists_affine_etale_refinement_of_smooth_cover 𝒰
  have hcontains (j : J) : B.Contains (A j) := by
    have := hAff j
    have := hEt j
    exact (Scheme.size_le_of_locallyOfFiniteType (p j)).trans_lt T₀.left.property
  let V : J → BigFppfOver B S hS := fun j =>
    Over.mk (ObjectProperty.homMk (p j ≫ B.inclusion.map T₀.hom) :
      B.obj (hcontains j) ⟶ B.obj hS)
  let π : ∀ j, V j ⟶ T₀ := fun j => Over.homMk (ObjectProperty.homMk (p j)) rfl
  have hVcov : IsEtaleCovering B S hS
      (fun j => yoneda.obj (V j)) (fun j => yoneda.map (π j)) :=
    isEtaleCovering_yoneda_of_etale B S hS V π (fun j => hEt j) (fun x => hAsurj x)
  have hatlas : IsEtaleCovering B S hS
      (fun _ : PUnit.{v + 1} => yoneda.obj T₀) (fun _ => b) :=
    isEtaleCovering_atlas B S hS hf.target_isAlgebraicSpace hbSurj hbEtale
  have hcomp := isEtaleCovering_comp B S hS (fun _ : PUnit.{v + 1} => J)
    (fun _ : PUnit.{v + 1} => yoneda.obj T₀) (fun _ => b)
    (fun _ j => yoneda.obj (V j)) (fun _ j => yoneda.map (π j)) hatlas fun _ => hVcov
  refine ⟨J, fun j => yoneda.obj (V j), fun j => yoneda.map (π j) ≫ b,
    IsEtaleCovering.reindex B S hS hcomp
      (σ := fun j : J => (⟨PUnit.unit, j⟩ : (_ : PUnit.{v + 1}) × J)) (fun c => ⟨c.2, rfl⟩),
    fun j => ?_⟩
  obtain ⟨⟨k, uk⟩, h, hh⟩ := hArefine j
  have hh' : h ≫ B.inclusion.map ((d ⟨k, uk⟩).left) = p j := hh
  have hsq : (q k).hom ≫ b = (pr k).hom ≫ f k :=
    congrArg (fun m : Y k ⟶ FObj => m.hom) (hpb k).w
  have hw : B.inclusion.map ((d ⟨k, uk⟩).left) ≫ B.inclusion.map (Over.hom T₀) =
      B.inclusion.map (Over.hom (W k)) := by
    rw [← Functor.map_comp, Over.w]
  have hwsite : (ObjectProperty.homMk h : B.obj (hcontains j) ⟶ (W k).left) ≫ (W k).hom =
      (V j).hom := by
    apply ObjectProperty.hom_ext
    show h ≫ B.inclusion.map (Over.hom (W k)) = p j ≫ B.inclusion.map (Over.hom T₀)
    rw [← hw, ← Category.assoc, hh']
  let hsite : V j ⟶ W k := Over.homMk (ObjectProperty.homMk h) hwsite
  have hsited : hsite ≫ d ⟨k, uk⟩ = π j := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hh')
  refine ⟨k, yoneda.map hsite ≫ w k ≫ (pr k).hom, ?_⟩
  show (yoneda.map hsite ≫ w k ≫ (pr k).hom) ≫ f k = yoneda.map (π j) ≫ b
  rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc (w k) ((q k).hom) b,
    ← hd ⟨k, uk⟩, ← Category.assoc, ← Functor.map_comp, hsited]

end AlgebraicGeometry.Space

end
