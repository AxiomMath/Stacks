module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeGeometricPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover

/-!
# The top-degree trace is an isomorphism once it is one on the geometric fibres

Let `p : Y ⟶ B` be proper with fibres of dimension `≤ 1`, `N ≥ 1`, and `c ∈ Ext²(Λ_Y, Λ_Y)`,
`Λ = ℤ/N`. The functor `T(G) = R²p_*(p⁻¹G)` is right exact: `R³p_*` vanishes on torsion sheaves
(Tag 095U). Hence the top-degree trace `ν : U ⟶ T` of `c`
(`Stacks.EtaleCohomology.TopTrace.trace`) is invertible at `G` once it is at the two free sheaves
of the presentation `Λ[K] ⟶ Λ[G] ⟶ G ⟶ 0`, and with the base change of the edge map
(`Stacks.EtaleCohomology.TopTrace.isIso_inverseImage_edge`) this reduces the invertibility of `ν`
at a geometric point `x̄` of `B` to that of the trace of the restricted class on the fibre over
`x̄`.

## Main results

* `Stacks.EtaleCohomology.TopTrace.isZero_homology_one_topObj`: `R³p_* = 0`.
* `Stacks.EtaleCohomology.TopTrace.topSheaf_exact`: `T` is right exact.
* `Stacks.EtaleCohomology.TopTrace.isIso_of_presentation`: a natural transformation of right
  exact functors invertible on a presentation is invertible.
* `Stacks.EtaleCohomology.TopTrace.isIso_inverseImage_trace`: the trace is invertible after base
  change once the base-changed edge maps are invertible on sheaves with flat fibres.
* `Stacks.EtaleCohomology.TopTrace.isIso_trace_of_fibres`: the trace is invertible once the edge
  maps on the geometric fibres are invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard
  isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Sheaf.monoidalCategory
  isMonoidal_W_etaleModules

/-! ### A natural transformation invertible on a presentation -/

section Presentation

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Preadditive 𝒜] [Abelian ℬ]
  {F₁ F₂ : 𝒜 ⥤ ℬ} [F₁.PreservesZeroMorphisms] [F₂.PreservesZeroMorphisms] (η : F₁ ⟶ F₂)

/-- **A natural transformation of additive functors invertible on a presentation is invertible.**
Let `P₁ ⟶ K ⟶ P₀ ⟶ G` with `K ⟶ P₀ ⟶ G` carried by `F₂` to an exact sequence, `P₁ ⟶ K` carried
by `F₂` to an epimorphism and `P₀ ⟶ G` carried by both functors to epimorphisms. If `η` is
invertible at `P₁` and `P₀` it is invertible at `G`. -/
theorem isIso_of_presentation {P₁ K P₀ G : 𝒜} (e : P₁ ⟶ K) (ι : K ⟶ P₀) (b : P₀ ⟶ G)
    (hιb : ι ≫ b = 0)
    (h₂ : (ShortComplex.mk (F₂.map ι) (F₂.map b) (by rw [← F₂.map_comp, hιb, F₂.map_zero])).Exact)
    [Epi (F₂.map e)] [Epi (F₁.map b)] [Epi (F₂.map b)] [IsIso (η.app P₁)] [IsIso (η.app P₀)] :
    IsIso (η.app G) := by
  let v : F₂.obj G ⟶ F₁.obj G := h₂.desc (inv (η.app P₀) ≫ F₁.map b) (by
    change F₂.map ι ≫ inv (η.app P₀) ≫ F₁.map b = 0
    rw [← cancel_epi (F₂.map e), ← Category.assoc, ← F₂.map_comp,
      ← cancel_epi (η.app P₁), ← Category.assoc, ← η.naturality (e ≫ ι), Category.assoc,
      IsIso.hom_inv_id_assoc, ← F₁.map_comp, Category.assoc, hιb, Limits.comp_zero, F₁.map_zero]
    simp)
  have hv : F₂.map b ≫ v = inv (η.app P₀) ≫ F₁.map b := h₂.g_desc _ _
  refine ⟨v, ?_, ?_⟩
  · rw [← cancel_epi (F₁.map b), ← Category.assoc, η.naturality b, Category.assoc, hv,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← cancel_epi (F₂.map b), ← Category.assoc, hv, Category.assoc, η.naturality b,
      IsIso.inv_hom_id_assoc, Category.comp_id]

end Presentation

/-! ### `R³p_*` vanishes and `T` is right exact -/

section Exact

variable {N : ℕ} {B Y : Scheme.{u}} (p : Y ⟶ B) [IsProper p]

include p in
/-- **`R³p_*` vanishes on `ℤ/N`-modules** when the fibres of the proper `p` have dimension `≤ 1`
(Tag 095U): `H¹(Rp_*(U F[2])) = R³p_*(U F) = 0`. -/
theorem isZero_homology_one_topObj (hfib : ∀ b : B, topologicalKrullDim (p.fiber b) ≤ 1)
    (hN : N ≠ 0) (F : EtaleModules.{u, 0} (ZMod N) Y) :
    IsZero ((DerivedCategory.homologyFunctor _ 1).obj ((etaleAbelianDerivedDirectImage.{u, 0} p).obj
      (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F))⟦((2 : ℕ) : ℤ)⟧))) := by
  let e1 := (DerivedCategory.homologyFunctor _ 1).mapIso
    (((etaleAbelianDerivedDirectImage.{u, 0} p).commShiftIso ((2 : ℕ) : ℤ)).app
      ((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F)))
  let e2 := ((DerivedCategory.homologyFunctor
    (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).shiftIso
      ((2 : ℕ) : ℤ) 1 ((3 : ℕ) : ℤ) (by norm_num)).app
      ((etaleAbelianDerivedDirectImage.{u, 0} p).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F)))
  let e3 := Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
    (etaleAbelianDirectImage.{u, 0} p) (etaleAbelianDerivedDirectImage.{u, 0} p)
    (etaleAbelianDerivedDirectImageUnit.{u, 0} p)
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)
    ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F) 3
  exact (isZero_rightDerived_etaleAbelianDirectImage_of_isProper p 1 hfib _
    (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero (ZMod N) N
      (Nat.pos_of_ne_zero hN) (ZMod.natCast_self N) F) 3 (by norm_num)).of_iso (e1 ≪≫ e2 ≪≫ e3)

/-- The image of a short complex under `T`. -/
def topSheafComplex (S : ShortComplex (EtaleModules.{u, 0} (ZMod N) B)) :
    ShortComplex (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI := topSheaf_preservesZeroMorphisms p (N := N)
  S.map (topSheaf p)

include p in
/-- **`T = R²p_* ∘ p⁻¹` is right exact** on a short exact sequence of sheaves of `ℤ/N`-modules,
when the fibres of the proper `p` have dimension `≤ 1`. -/
theorem topSheaf_exact (hfib : ∀ b : B, topologicalKrullDim (p.fiber b) ≤ 1) (hN : N ≠ 0)
    {S : ShortComplex (EtaleModules.{u, 0} (ZMod N) B)} (hS : S.ShortExact) :
    (topSheafComplex p S).Exact ∧ Epi ((topSheaf p).map S.g) := by
  have i1 : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} (ZMod N) p) :=
    etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod N) p
  have i2 : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} (ZMod N) p) :=
    etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod N) p
  have i3 : (etaleModuleInverseImage.{u, 0} (ZMod N) p).IsLeftAdjoint :=
    ⟨_, ⟨etaleModuleInverseImageAdj.{u, 0} (ZMod N) p⟩⟩
  have i0 : (etaleModuleInverseImage.{u, 0} (ZMod N) p).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hS1 : (S.map (etaleModuleInverseImage.{u, 0} (ZMod N) p)).ShortExact :=
    hS.map_of_exact (F := etaleModuleInverseImage.{u, 0} (ZMod N) p)
  let S' := (S.map (etaleModuleInverseImage.{u, 0} (ZMod N) p)).map
    (etaleModuleUnderlyingAbelian Y (ZMod N))
  have hS' : S'.ShortExact := hS1.map_of_exact (F := etaleModuleUnderlyingAbelian Y (ZMod N))
  let T := (etaleAbelianDerivedDirectImage.{u, 0} p).mapTriangle.obj
    ((Pretriangulated.Triangle.shiftFunctor _ ((2 : ℕ) : ℤ)).obj hS'.singleTriangle)
  have hT : T ∈ distTriang _ := (etaleAbelianDerivedDirectImage.{u, 0} p).map_distinguished _
    (Pretriangulated.Triangle.shift_distinguished _ hS'.singleTriangle_distinguished _)
  have key : ∀ {X Z : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
      (u : X ⟶ Z), (etaleAbelianDerivedDirectImage.{u, 0} p).map
        ((((2 : ℕ) : ℤ)).negOnePow • u⟦((2 : ℕ) : ℤ)⟧') =
      (etaleAbelianDerivedDirectImage.{u, 0} p).map (u⟦((2 : ℕ) : ℤ)⟧') := fun u => by
    rw [show (((2 : ℕ) : ℤ)).negOnePow = 1 by decide, one_smul]
  have h1 : T.mor₁ = (etaleAbelianDerivedDirectImage.{u, 0} p).map
      (((DerivedCategory.singleFunctor _ 0).map S'.f)⟦((2 : ℕ) : ℤ)⟧') := key _
  have h2 : T.mor₂ = (etaleAbelianDerivedDirectImage.{u, 0} p).map
      (((DerivedCategory.singleFunctor _ 0).map S'.g)⟦((2 : ℕ) : ℤ)⟧') := key _
  refine ⟨?_, ?_⟩
  · refine (ShortComplex.exact_iff_of_iso ?_).1 (DerivedCategory.HomologySequence.exact₂ T hT 0)
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp only [Iso.refl_hom]
      rw [h1]
      rfl
    · simp only [Iso.refl_hom]
      rw [h2]
      rfl
  · have he := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1 rfl).2
      ((isZero_homology_one_topObj p hfib hN _).eq_of_tgt _ _)
    change Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((etaleAbelianDerivedDirectImage.{u, 0} p).map
        (((DerivedCategory.singleFunctor _ 0).map S'.g)⟦((2 : ℕ) : ℤ)⟧')))
    rwa [← h2]

end Exact

/-! ### Reduction to the geometric fibres -/

section Fibres

variable {N : ℕ} {B Y B' Y' : Scheme.{u}} (p : Y ⟶ B) [IsProper p] (g : B' ⟶ B) (g' : Y' ⟶ Y)
  (p' : Y' ⟶ B') (sq : IsPullback g' p' p g)
  (c : Ext.{u + 1} (MonoidalCategory.tensorUnit (EtaleModules.{u, 0} (ZMod N) Y))
    (MonoidalCategory.tensorUnit _) 2)

include sq in
/-- **The trace is invertible after base change** at every sheaf, as soon as the base-changed edge
maps are invertible at the inverse images of sheaves with flat fibres. -/
theorem isIso_inverseImage_trace (hfib : ∀ b : B, topologicalKrullDim (p.fiber b) ≤ 1)
    (hN : N ≠ 0)
    (hA : ∀ (A : EtaleModules.{u, 0} (ZMod N) B) (hA : FlatFibres A),
      IsIso (edge p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p')))
    (G : EtaleModules.{u, 0} (ZMod N) B) :
    IsIso ((etaleAbelianInverseImage.{u, 0} g).map ((trace p c).app G)) := by
  let η := Functor.whiskerRight (trace p c) (etaleAbelianInverseImage.{u, 0} g)
  change IsIso (η.app G)
  let K := kernel (freeCoverπ G)
  have hSE : ∀ X : EtaleModules.{u, 0} (ZMod N) B,
      (ShortComplex.mk (kernel.ι (freeCoverπ X)) (freeCoverπ X) (kernel.condition _)).ShortExact :=
    fun X => by
      have := epi_freeCoverπ X
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel
        (ShortComplex.mk (kernel.ι (freeCoverπ X)) (freeCoverπ X) (kernel.condition _))
        (kernelIsKernel (freeCoverπ X))) (by dsimp; infer_instance) (by dsimp; infer_instance)
  obtain ⟨hex, hepi⟩ := topSheaf_exact p hfib hN (hSE G)
  obtain ⟨-, hepiK⟩ := topSheaf_exact p hfib hN (hSE K)
  have := epi_map_freeCoverπ G
  have hfree : ∀ X : EtaleModules.{u, 0} (ZMod N) B, IsIso (η.app (freeCover X)) := fun X => by
    change IsIso ((etaleAbelianInverseImage.{u, 0} g).map ((trace p c).app (freeCover X)))
    rw [trace_app_eq_edge p c _ (flatFibres_inverseImage_freeCover p X)]
    exact isIso_inverseImage_edge g' c p g p' sq.w hN sq _ (flatFibres_free _)
      (hA _ (flatFibres_free _))
  have := hfree G
  have := hfree K
  have : Epi ((etaleModuleUnderlyingAbelian B (ZMod N) ⋙ etaleAbelianInverseImage.{u, 0} g).map
      (freeCoverπ G)) := by
    change Epi ((etaleAbelianInverseImage.{u, 0} g).map
      ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G)))
    infer_instance
  have : Epi ((topSheaf p ⋙ etaleAbelianInverseImage.{u, 0} g).map (freeCoverπ G)) := by
    change Epi ((etaleAbelianInverseImage.{u, 0} g).map ((topSheaf p).map (freeCoverπ G)))
    infer_instance
  have : Epi ((topSheaf p ⋙ etaleAbelianInverseImage.{u, 0} g).map (freeCoverπ K)) := by
    change Epi ((etaleAbelianInverseImage.{u, 0} g).map ((topSheaf p).map (freeCoverπ K)))
    infer_instance
  have := topSheaf_preservesZeroMorphisms p (N := N)
  exact isIso_of_presentation η (freeCoverπ K) (kernel.ι (freeCoverπ G)) (freeCoverπ G)
    (kernel.condition _) (hex.map (etaleAbelianInverseImage.{u, 0} g))

omit [IsProper p] in
include p in
/-- **The trace is invertible once it is on the geometric fibres**: if at every point `b` of `B`
the edge maps of the restriction of `c` to the fibre `Y_b̄` over the geometric point `b̄` are
invertible at the restrictions of sheaves with flat fibres, the trace `ν` of `c` is invertible at
every sheaf of `ℤ/N`-modules. -/
theorem isIso_trace_of_fibres [IsProper p] (hfib : ∀ b : B, topologicalKrullDim (p.fiber b) ≤ 1)
    (hN : N ≠ 0)
    (c : Ext.{u + 1} (MonoidalCategory.tensorUnit (EtaleModules.{u, 0} (ZMod N) Y))
      (MonoidalCategory.tensorUnit _) 2)
    (hA : ∀ (b : B) (A : EtaleModules.{u, 0} (ZMod N) B) (hA : FlatFibres A),
      IsIso (edge (pullback.snd p (GeometricPoint.ofPoint B b).hom)
        (pullClass (pullback.fst p (GeometricPoint.ofPoint B b).hom) c)
          ((etaleModuleInverseImage.{u, 0} (ZMod N) (GeometricPoint.ofPoint B b).hom).obj A)
          ((hA.inverseImage _).inverseImage _)))
    (G : EtaleModules.{u, 0} (ZMod N) B) : IsIso ((trace p c).app G) := by
  refine isIso_of_geometricStalkAb_family
    (Ω := fun b : B => (GeometricPoint.ofPoint B b).residueField)
    (fun b => (GeometricPoint.ofPoint B b).hom) ?_ _ (fun b => ?_)
  · exact Set.eq_univ_of_forall fun b =>
      Set.mem_iUnion.2 ⟨b, default, GeometricPoint.ofPoint_liesOver B b⟩
  · exact isIso_stalk_of_isIso_etaleAbelianInverseImage_map (GeometricPoint.ofPoint B b) _
      (isIso_inverseImage_trace p _ _ _ (IsPullback.of_hasPullback p _) c hfib hN (hA b) G)

end Fibres

end Stacks.EtaleCohomology.TopTrace
