module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.PartialIdeal
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.FibrewiseSmoothness
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal

/-!
# One step of the tower of partial intersections, on a fibre

The flatness of the family `V(v₁ - t₁ w₀, …) ⊆ X̄ × 𝔸^{d-1}` near the fibre through the point is
proved one equation at a time ([Stacks, Tag 062Y] (3),
`AlgebraicGeometry.exists_flat_zeroScheme_of_fibre`), and each step asks for an integral open of
the previous partial intersection in the fibre on which the next section does not vanish
identically. This file produces that open from the dimensions: if `V(I)` is smooth of relative
dimension `r + 1` near `z` and `V(I) ∩ V(g)` is smooth of relative dimension `r` there, then near
`z` the section `g` is nonzero on an integral open of `V(I)` — otherwise `V(I) ∩ V(g)` would
contain a neighbourhood of `z` in `V(I)` and so have dimension `r + 1` at `z`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_isIntegral_opens_of_isNormal`: a point of a normal
  locally Noetherian scheme has an integral open neighbourhood.
* `AlgebraicGeometry.GoodNeighbourhood.topologicalKrullDimAt_fiber_eq_of_subsingleton`: over a
  one-point base the fibre is the whole scheme, dimensionwise.
* `AlgebraicGeometry.GoodNeighbourhood.exists_topologicalKrullDimAt_eq_of_subschemeSmoothAt`.
* `AlgebraicGeometry.GoodNeighbourhood.exists_isIntegral_ne_zero_of_subschemeSmoothAt`.
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **A point of a normal locally Noetherian scheme has an integral open neighbourhood**: such a
scheme is a disjoint union of normal integral schemes ([Stacks, Tag 0357]). -/
theorem exists_isIntegral_opens_of_isNormal (Y : Scheme.{u}) [IsNormal Y] [IsLocallyNoetherian Y]
    (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ IsIntegral W.toScheme := by
  have hcomp : ∀ V : Y.Opens, IsCompact (V : Set Y) → (irreducibleComponents V).Finite :=
    fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact finite_irreducibleComponents_of_isNoetherian
  obtain ⟨ι, W, -, hWi, ⟨e⟩⟩ := (isNormal_iff_exists_iso_coproduct hcomp).mp inferInstance
  obtain ⟨⟨i, z⟩, hz⟩ := (AlgebraicGeometry.sigmaMk W).surjective (e.hom y)
  let g := Limits.Sigma.ι W i ≫ e.inv
  have : IsIntegral (W i) := hWi i
  refine ⟨g.opensRange, ⟨z, ?_⟩, IsIntegral.of_isIso
    (IsOpenImmersion.isoOfRangeEq g g.opensRange.ι (by simp)).hom⟩
  have h : (Limits.Sigma.ι W i) z = e.hom y := by simpa only [sigmaMk_mk] using hz
  show e.inv ((Limits.Sigma.ι W i) z) = y
  rw [h]
  exact congrArg (fun k : Y ⟶ Y => k y) e.hom_inv_id

/-- **Over a one-point base the fibre is the whole scheme**, as far as local dimensions go. -/
theorem topologicalKrullDimAt_fiber_eq_of_subsingleton {Y S : Scheme.{u}} (q : Y ⟶ S)
    [Subsingleton S] (y : Y) :
    topologicalKrullDimAt (q.fiber (q y)) (q.asFiber y) = topologicalKrullDimAt Y y := by
  rw [topologicalKrullDimAt_eq_of_homeomorph (q.fiberHomeo (q y)) (q.asFiber y)]
  have hP : IsOpen (q.base ⁻¹' {q y}) := by
    have : ({q y} : Set S) = Set.univ :=
      Set.eq_univ_of_forall fun t => Subsingleton.elim t (q y)
    rw [this, Set.preimage_univ]
    exact isOpen_univ
  rw [← hP.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq
    (q.fiberHomeo (q y) (q.asFiber y))]
  congr 1
  rw [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]

/-- **The local dimension of a closed subscheme smooth of relative dimension `n` over a one-point
base is `n`.** -/
theorem exists_topologicalKrullDimAt_eq_of_subschemeSmoothAt {X S : Scheme.{u}} (q : X ⟶ S)
    [Subsingleton S] {I : X.IdealSheafData} {n : ℕ} {z : X} (h : SubschemeSmoothAt q I n z) :
    ∃ y : I.subscheme, I.subschemeι y = z ∧ ∃ U : I.subscheme.Opens, y ∈ U ∧
      SmoothOfRelativeDimension n (U.ι ≫ I.subschemeι ≫ q) ∧
      topologicalKrullDimAt I.subscheme y = (n : WithBot ℕ∞) := by
  obtain ⟨y, hy, U, hyU, hsm⟩ := h
  refine ⟨y, hy, U, hyU, hsm, ?_⟩
  calc topologicalKrullDimAt I.subscheme y
      = topologicalKrullDimAt U.toScheme ⟨y, hyU⟩ := by
        simpa only [Scheme.Opens.ι_apply] using
          U.ι.isOpenEmbedding.topologicalKrullDimAt_eq (⟨y, hyU⟩ : U.toScheme)
    _ = _ := (topologicalKrullDimAt_fiber_eq_of_subsingleton (U.ι ≫ I.subschemeι ≫ q) _).symm
    _ = (n : WithBot ℕ∞) :=
      fiberDimensionAt_eq_of_smoothOfRelativeDimension (U.ι ≫ I.subschemeι ≫ q) n ⟨y, hyU⟩

/-- **The next section does not vanish on an integral open of the previous partial
intersection.** Let `q : Y ⟶ S` with `S` a normal one-point scheme (the spectrum of a field), let
`I` be an ideal sheaf on `Y` and `g` a section of an invertible module. If `V(I)` is smooth of
relative dimension `r + 1` near `z` and `V(I) ∩ V(g)` is smooth of relative dimension `r` near
`z`, then the point of `V(I)` over `z` has an integral open neighbourhood in `V(I)` on which the
pullback of `g` is nonzero. -/
theorem exists_isIntegral_ne_zero_of_subschemeSmoothAt {Y S : Scheme.{u}} (q : Y ⟶ S)
    [Subsingleton S] [IsNormal S] (I : Y.IdealSheafData) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] (g : Γ(L, ⊤)) (r : ℕ)
    (z : Y) (h₁ : SubschemeSmoothAt q I (r + 1) z)
    (h₂ : SubschemeSmoothAt q (I ⊔ zeroScheme Y L g) r z) :
    ∃ (y₀ : I.subscheme) (U : I.subscheme.Opens), I.subschemeι y₀ = z ∧ y₀ ∈ U ∧
      IsIntegral U.toScheme ∧ pullbackGlobalSections (U.ι ≫ I.subschemeι) L g ≠ 0 := by
  obtain ⟨y₀, hy₀, U₁, hyU₁, hsm₁, hdim₁⟩ :=
    exists_topologicalKrullDimAt_eq_of_subschemeSmoothAt q h₁
  obtain ⟨y', hy', -, -, -, hdim₂⟩ := exists_topologicalKrullDimAt_eq_of_subschemeSmoothAt q h₂
  have : Smooth (U₁.ι ≫ I.subschemeι ≫ q) := SmoothOfRelativeDimension.smooth (r + 1) _
  have : IsNormal U₁.toScheme := isNormal_of_smooth (U₁.ι ≫ I.subschemeι ≫ q)
  have : IsLocallyNoetherian U₁.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U₁.ι ≫ I.subschemeι ≫ q)
  obtain ⟨W, hyW, hW⟩ := exists_isIntegral_opens_of_isNormal U₁.toScheme ⟨y₀, hyU₁⟩
  let e := W.ι ≫ U₁.ι
  let U := e.opensRange
  have : IsIntegral U.toScheme :=
    IsIntegral.of_isIso (IsOpenImmersion.isoOfRangeEq e U.ι (by rw [Scheme.Opens.range_ι]; rfl)).hom
  let w : W.toScheme := ⟨(⟨y₀, hyU₁⟩ : U₁.toScheme), hyW⟩
  have hyU : y₀ ∈ U := ⟨w, rfl⟩
  refine ⟨y₀, U, hy₀, hyU, this, fun h0 => ?_⟩
  -- otherwise `V(I) ∩ V(g)` contains `U`, of dimension `r + 1` at `y₀`
  have hsupp : ∀ u : U.toScheme, I.subschemeι (U.ι u) ∈ (I ⊔ zeroScheme Y L g).support := by
    intro u
    rw [Scheme.IdealSheafData.support_sup]
    refine ⟨by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩, ?_⟩
    have hc : (zeroScheme Y L g).comap (U.ι ≫ I.subschemeι) = ⊥ := by
      rw [← Stacks.Divisors.zeroScheme_pullback, h0, Stacks.Divisors.zeroScheme_zero_eq_bot]
    have hu : u ∈ ((zeroScheme Y L g).comap (U.ι ≫ I.subschemeι)).support := by
      rw [hc, Scheme.IdealSheafData.support_bot]
      trivial
    rwa [Scheme.IdealSheafData.support_comap] at hu
  let hom := (I ⊔ zeroScheme Y L g).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  let ψ : U.toScheme → Set.range (I ⊔ zeroScheme Y L g).subschemeι.base := fun u =>
    ⟨I.subschemeι (U.ι u), by rw [Scheme.IdealSheafData.range_subschemeι]; exact hsupp u⟩
  have hψ : IsEmbedding ψ := by
    rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact (I.subschemeι.isClosedEmbedding.isEmbedding.comp U.ι.isOpenEmbedding.isEmbedding :
      IsEmbedding (fun u : U.toScheme => I.subschemeι (U.ι u)))
  let u₀ : U.toScheme := ⟨y₀, hyU⟩
  have hle := topologicalKrullDimAt_le_of_isEmbedding (hom.symm.isEmbedding.comp hψ) u₀
  have hpt : (hom.symm ∘ ψ) u₀ = y' := by
    apply hom.injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact Subtype.ext (hy₀.trans hy'.symm)
  have hdimU : topologicalKrullDimAt U.toScheme u₀ = ((r + 1 : ℕ) : WithBot ℕ∞) :=
    (U.ι.isOpenEmbedding.topologicalKrullDimAt_eq u₀).symm.trans hdim₁
  rw [hpt, hdimU, hdim₂] at hle
  exact absurd hle (by exact_mod_cast Nat.not_succ_le_self r)

end AlgebraicGeometry.GoodNeighbourhood

end
