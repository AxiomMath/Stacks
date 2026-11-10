module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringLimitDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Filtered.Final

/-!
# A single fppf covering at a finite stage along which an object over the limit lifts

Let `a : 𝒲 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf category of
`S` which is locally essentially surjective in the fppf topology through flat, locally finitely
presented, surjective morphisms: every object of `𝒳` over `U` is, after base change along such a
morphism `T ⟶ U`, the image of an object of `𝒲` (the hypothesis of
`AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`, satisfied by a smooth atlas). Let
`T = lim Tᵢ` be a cofiltered limit of affine schemes over `S`. Then every object `x` of `𝒳` over
`T` lifts to `𝒲` after base change along `W₀ ×_{Tᵢ₀} T ⟶ T` for a single affine `W₀` with a
morphism `W₀ ⟶ Tᵢ₀` defined at a finite stage `i₀`, every base change of which generates a covering
sieve. This is the first step of the proof of Stacks 0CMX, and of the implication (3) ⟹ (1) of
Stacks 0CMY, in which the object over the limit is descended to a stage: the cover on which it
lifts to an atlas is itself descended first.

## Main results

* `AlgebraicGeometry.Stack.exists_singleCover_lift`.

## Implementation notes

The lift over `T` is refined to a finite standard fppf covering of `T` (Stacks 021P), whose
disjoint union `∐ Xₖ ⟶ T` is one affine flat morphism of finite presentation through which the
lift factors (Stacks 03FI, 03OZ). That single morphism descends to a stage by Stacks 049N, applied
to the diagram over the given index `i` so that the stage comes with a map to `i`. The descended
scheme is contained in the site, being of finite presentation over a contained scheme
(Stacks 000R), and its fibre product with `T` over the stage is, by Stacks 021U, the fibre
product in the site, which is isomorphic over `T` to the disjoint union; the lift is pulled back
along it. Every base change of the descended morphism is flat, locally of finite presentation and
surjective, so it generates a covering sieve.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

/-- **An object over a cofiltered limit of affine schemes lifts to an atlas after base change
along a single fppf covering defined at a finite stage.** See the module documentation. -/
theorem exists_singleCover_lift (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒲 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒲 ⟶ 𝒳)
    (H : ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left), Flat (B.inclusion.map m) ∧
        LocallyOfFinitePresentation (B.inclusion.map m) ∧ Surjective (B.inclusion.map m) ∧
        ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ y.1),
          𝒳.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    (x : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt)) :
    ∃ (i₀ : I) (_s₀ : i₀ ⟶ i) (W₀ : BigFppfOver B S hS) (_ : IsAffineOver B S hS W₀)
      (w : W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)),
      (∀ (Z : BigFppfOver B S hS) (g : Z ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)),
        Sieve.ofArrows (fun _ : Unit => pullback w g) (fun _ => pullback.snd w g) ∈
          BigFppfOver.topology B S hS Z) ∧
      ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor a).obj z ⟶ x.1),
        𝒳.val.p.IsHomLift
          (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (c.π.app i₀))) φ := by
  classical
  let inc := BigAffineFppf.inclusion B S hS
  let toSch := BigFppfOver.toScheme B S hS
  let affSch := BigAffineFppf.toScheme B S hS
  let T := inc.obj c.pt
  have hTaff : IsAffine (B.inclusion.obj T.left) := c.pt.property
  -- The lift over `T`.
  obtain ⟨T', m, hflat, hlfp, hsurj, z, φ, hφ⟩ := H T x
  -- A finite standard fppf refinement of `{m}`.
  have hR : Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{u + 2} => T') (fun _ => m)) ∈
      B.topology T.left := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [bigFppfPrecoverage_eq_comap B, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun y => ⟨PUnit.unit, hsurj.surj y⟩, fun _ => ⟨hflat, hlfp⟩⟩
  obtain ⟨Q, -, hQstd, hQR⟩ := exists_standardFppf_refinement B hR
  have hfac : ∀ k : Q.I₀, ∃ g : Q.X k ⟶ T', g ≫ m = Q.f k := by
    intro k
    obtain ⟨Y, h, g, hg, hhg⟩ := hQR _ _ (Presieve.ofArrows.mk k)
    obtain ⟨⟩ := hg
    exact ⟨h, hhg⟩
  choose g hg using hfac
  have : Finite Q.I₀ := hQstd.finite_index
  let Xs : Q.I₀ → Scheme.{u} := fun k => B.inclusion.obj (Q.X k)
  let fs : ∀ k, Xs k ⟶ B.inclusion.obj T.left := fun k => B.inclusion.map (Q.f k)
  have hstd : IsStandardCovering .fppf Xs fs :=
    { finite_index := hQstd.finite_index
      affine_source := hQstd.affine_source
      jointly_surjective := hQstd.jointly_surjective
      standard := fun k => ⟨hQstd.flat k, hQstd.finite_presentation k⟩ }
  let Ws : Scheme.{u} := ∐ Xs
  let fW : Ws ⟶ B.inclusion.obj T.left := Sigma.desc fs
  have hWaff : IsAffine Ws := hstd.isAffine_sigmaObj .fppf Xs fs
  have hfW := (Scheme.singleton_mem_precoverage_iff (coveringMorphismProperty .fppf) fW).mp
    (hstd.singleton_sigmaDesc_mem_precoverage .fppf (by decide) Xs fs)
  have hfWflat : Flat fW := hfW.2.1
  have hfWlfp : LocallyOfFinitePresentation fW := hfW.2.2
  have hfWfp : FinitePresentation fW := FinitePresentation.mk hfWlfp inferInstance inferInstance
  -- The factorisation of the disjoint union through the lift.
  let G : Ws ⟶ B.inclusion.obj T' := Sigma.desc fun k => B.inclusion.map (g k)
  have hG : G ≫ B.inclusion.map m = fW := by
    refine Sigma.hom_ext _ _ fun k => ?_
    rw [Sigma.ι_comp_desc_assoc, ← B.inclusion.map_comp, hg k, Sigma.ι_comp_desc]
  -- Descend the single morphism to a stage over `i`.
  let D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D ⋙ affSch
  let c' : Cone D' := (affSch.mapCone c).whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc
  have : ∀ j, IsAffine (D'.obj j) := fun j => (D.obj j.left).property
  have : IsAffine c'.pt := c.pt.property
  have hstd₁ : IsStandardCovering .fppf (fun _ : Unit => Ws) (fun _ => fW) :=
    { finite_index := inferInstance
      affine_source := fun _ => hWaff
      jointly_surjective := Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨(), hfW.1 y⟩
      standard := fun _ => ⟨hfWflat, hfWfp⟩ }
  obtain ⟨j₀, U₀, f₀, hf₀, he⟩ :=
    exists_isStandardCovering_of_isLimit .fppf D' c' hc' (fun _ : Unit => Ws) (fun _ => fW)
      hstd₁
  obtain ⟨e⟩ := he ()
  let i₀ := j₀.left
  have hf₀flat : Flat (f₀ ()) := (hf₀.standard ()).1
  have hf₀fp : FinitePresentation (f₀ ()) := (hf₀.standard ()).2
  have : LocallyOfFinitePresentation (f₀ ()) := hf₀fp.locallyOfFinitePresentation
  have : QuasiCompact (f₀ ()) := hf₀fp.quasiCompact
  -- The descended scheme belongs to the site.
  have hU₀ : B.Contains (U₀ ()) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (f₀ ())
      ((inc.obj (D.obj i₀)).left.property)
  let w₀ : B.obj hU₀ ⟶ (inc.obj (D.obj i₀)).left := ObjectProperty.homMk (f₀ ())
  let W₀ : BigFppfOver B S hS := Over.mk (w₀ ≫ (inc.obj (D.obj i₀)).hom)
  let w : W₀ ⟶ inc.obj (D.obj i₀) := Over.homMk w₀
  have htoSchw : toSch.map w = f₀ () := rfl
  have hWaff₀ : IsAffineOver B S hS W₀ := hf₀.affine_source ()
  -- Base changes of `w` are flat, locally finitely presented and surjective.
  have hbc : ∀ {Z : BigFppfOver B S hS} (g : Z ⟶ inc.obj (D.obj i₀)),
      Flat (toSch.map (pullback.snd w g)) ∧
        LocallyOfFinitePresentation (toSch.map (pullback.snd w g)) ∧
        Surjective (toSch.map (pullback.snd w g)) := by
    intro Z g
    have hpb : IsPullback (toSch.map (pullback.fst w g)) (toSch.map (pullback.snd w g))
        (toSch.map w) (toSch.map g) :=
      toSch.map_isPullback (IsPullback.of_hasPullback w g)
    have hw₁ : Flat (toSch.map w) := hf₀flat
    have hw₂ : LocallyOfFinitePresentation (toSch.map w) := hf₀fp.locallyOfFinitePresentation
    have hw₃ : Surjective (toSch.map w) := ⟨fun y => by
      have hy : y ∈ ⋃ u, Set.range (f₀ u) := hf₀.jointly_surjective ▸ Set.mem_univ y
      obtain ⟨⟨⟩, hu⟩ := Set.mem_iUnion.mp hy
      exact hu⟩
    exact ⟨MorphismProperty.of_isPullback hpb hw₁, MorphismProperty.of_isPullback hpb hw₂,
      MorphismProperty.of_isPullback hpb hw₃⟩
  refine ⟨i₀, j₀.hom, W₀, hWaff₀, w, ?_, ?_⟩
  · -- Every base change of `w` generates a covering sieve.
    intro Z g
    obtain ⟨h₁, h₂, h₃⟩ := hbc g
    have hmem := mem_topology_of_family B S hS (U := Z)
      (fun _ : PUnit.{u + 2} => (pullback w g).left) (fun _ => (pullback.snd w g).left)
      (fun _ => h₁) (fun _ => h₂) (fun y => ⟨PUnit.unit, h₃.surj y⟩)
    refine GrothendieckTopology.superset_covering _ ?_ hmem
    rw [Sieve.generate_le_iff]
    rintro V k ⟨⟩
    refine ⟨pullback w g, Over.homMk (𝟙 _) (by simp [Over.w (pullback.snd w g)]),
      pullback.snd w g, ⟨()⟩, ?_⟩
    ext
    simp
  · -- The lift, pulled back along the fibre product.
    let gπ := inc.map (c.π.app i₀)
    let P := pullback w gπ
    let π₂ : P ⟶ T := pullback.snd w gπ
    have hgπ : toSch.map gπ = c'.π.app j₀ := rfl
    let κ : toSch.obj P ⟶ Ws :=
      (PreservesPullback.iso toSch w gπ).hom ≫ e.hom.left
    have hκ : κ ≫ fW = toSch.map π₂ :=
      (Category.assoc _ _ _).trans ((congrArg ((PreservesPullback.iso toSch w gπ).hom ≫ ·)
        (Over.w e.hom)).trans (PreservesPullback.iso_hom_snd toSch w gπ))
    let kl : P.left ⟶ T' := B.inclusion.preimage (κ ≫ G)
    have hkl : kl ≫ m = π₂.left := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, Functor.map_preimage, Category.assoc, hG, hκ]
      rfl
    let k : P ⟶ (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) :=
      Over.homMk kl (by
        change kl ≫ m ≫ T.hom = P.hom
        rw [← Category.assoc, hkl, Over.w π₂])
    have hk : k ≫ (Over.homMk m rfl : (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) ⟶ T) = π₂ :=
      Over.OverMorphism.ext hkl
    let : 𝒲.val.p.IsFibered := 𝒲.2.isFibered
    have hz : 𝒲.val.p.obj z = (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) := by
      have h1 := Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) z
      exact h1.symm.trans (IsHomLift.domain_eq 𝒳.val.p
        (Over.homMk m rfl : (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) ⟶ T) φ)
    let ψ := Functor.IsPreFibered.pullbackMap hz k
    have hψ : 𝒲.val.p.IsHomLift k ψ := inferInstance
    have hψ' : 𝒳.val.p.IsHomLift k ((CatFiberedInGroupoids.homFunctor a).map ψ) :=
      Functor.isHomLift_map_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p a) k ψ
    refine ⟨Functor.IsPreFibered.pullbackObj hz k,
      (CatFiberedInGroupoids.homFunctor a).map ψ ≫ φ, ?_⟩
    have hfin : 𝒳.val.p.IsHomLift
        (k ≫ (Over.homMk m rfl : (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) ⟶ T))
        ((CatFiberedInGroupoids.homFunctor a).map ψ ≫ φ) := inferInstance
    rw [hk] at hfin
    exact hfin

end AlgebraicGeometry.Stack

end
