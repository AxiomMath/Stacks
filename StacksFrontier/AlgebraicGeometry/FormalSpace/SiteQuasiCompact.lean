module

public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# Compact schemes are quasi-compact objects of the big fppf site

A scheme whose underlying space is compact is a quasi-compact object of the big fppf site, and
likewise for a scheme over a base: any covering of it admits a finite subcovering, because an
fppf covering of a compact scheme can be refined by a finite one.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactObject_of_compact_scheme`
* `AlgebraicGeometry.FormalSpace.isQuasiCompactObject_over_of_compact_scheme`
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u w w₁ w₂

namespace AlgebraicGeometry.FormalSpace

public theorem isQuasiCompactObject_of_compact_scheme (B : BigFppfSite.{u})
    (T : B.Schemes) [CompactSpace (B.inclusion.obj T)] :
    B.topology.IsQuasiCompactObject T := by
  intro 𝒰 h𝒰
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B h𝒰
  have hEfp' : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) := by
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using B.isFppfCovering_of_isCovering hE
  have h𝒲 := (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hEfp'
  let image (i : E.I₀) : Set (B.inclusion.obj T) := Set.range ((E.map B.inclusion).f i)
  have himage_open (i : E.I₀) : IsOpen (image i) := by
    have : Flat ((E.map B.inclusion).f i) := (h𝒲.2 i).1
    have : LocallyOfFinitePresentation ((E.map B.inclusion).f i) := (h𝒲.2 i).2
    exact (Scheme.Hom.isOpenMap ((E.map B.inclusion).f i)).isOpen_range
  have himage_cover : Set.univ ⊆ ⋃ i, image i := by
    intro x _
    obtain ⟨i, y, hy⟩ := h𝒲.1 x
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hy⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover image himage_open himage_cover
  let V : PreZeroHypercover T :=
    ⟨{i : E.I₀ // i ∈ s}, fun i => E.X i.1, fun i => E.f i.1⟩
  have hVfp : (V.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).2
      ⟨fun x => ?_, fun i => h𝒲.2 i.1⟩
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, image, Set.mem_range] at hx
    obtain ⟨i, hi, y, hy⟩ := hx
    exact ⟨⟨i, hi⟩, y, hy⟩
  have hVfp' : IsFppfCovering ⟨T, V⟩ := by
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hVfp
  have hVcard : Cardinal.mk V.I₀ ≤ B.coveringBound :=
    (Cardinal.mk_le_of_injective (f := fun i : V.I₀ => i.1)
      fun _ _ => Subtype.ext).trans hE.2
  have hV : B.IsCovering ⟨T, V⟩ := ⟨hVfp', hVcard⟩
  have hVmem : V.sieve₀ ∈ B.topology T :=
    Precoverage.generate_mem_toGrothendieck (⟨V, rfl, hV⟩ : V.presieve₀ ∈ B.precoverage T)
  choose j α hα using fun i : V.I₀ =>
    (Sieve.mem_ofArrows_iff _ _ _).1
      (hER _ _ (PreZeroHypercover.presieve₀_f E i.1))
  exact ⟨V, { s₀ := j, h₀ := α, w₀ := fun i => (hα i).symm }, hVmem, Set.finite_range j⟩

public theorem isQuasiCompactObject_over_of_compact_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    (BigFppfOver.topology B S hS).IsQuasiCompactObject U := by
  intro 𝒰 h𝒰
  let 𝒰' : PreZeroHypercover U.left := {
    I₀ := 𝒰.I₀
    X i := (𝒰.X i).left
    f i := (𝒰.f i).left
  }
  have hbase' : 𝒰'.sieve₀ ∈ B.topology U.left := by
    rwa [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_ofArrows] at h𝒰
  have : CompactSpace (B.inclusion.obj U.left) := by
    show CompactSpace ((BigFppfOver.toScheme B S hS).obj U)
    infer_instance
  obtain ⟨E, ψ, hE, hfin⟩ :=
    isQuasiCompactObject_of_compact_scheme B U.left 𝒰' hbase'
  let V : PreZeroHypercover U := {
    I₀ := E.I₀
    X i := Over.mk (E.f i ≫ U.hom)
    f i := Over.homMk (E.f i)
  }
  have hV : V.sieve₀ ∈ BigFppfOver.topology B S hS U := by
    rwa [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_ofArrows]
  let φ : V.Hom 𝒰 := {
    s₀ := ψ.s₀
    h₀ := fun i => Over.homMk (ψ.h₀ i) (by
      have hw := ψ.w₀ i
      change ψ.h₀ i ≫ (𝒰.f (ψ.s₀ i)).left = E.f i at hw
      calc
        ψ.h₀ i ≫ (𝒰.X (ψ.s₀ i)).hom =
            (ψ.h₀ i ≫ (𝒰.f (ψ.s₀ i)).left) ≫ U.hom := by
              rw [Category.assoc, (𝒰.f (ψ.s₀ i)).w]
        _ = E.f i ≫ U.hom := by rw [hw])
    w₀ := fun i => by
      apply (Over.forget (B.obj hS)).map_injective
      show ψ.h₀ i ≫ (𝒰.f (ψ.s₀ i)).left = E.f i
      exact ψ.w₀ i
  }
  refine ⟨V, φ, hV, ?_⟩
  simpa [φ, 𝒰'] using hfin

end AlgebraicGeometry.FormalSpace

end
