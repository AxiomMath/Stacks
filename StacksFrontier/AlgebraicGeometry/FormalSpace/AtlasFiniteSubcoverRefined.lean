module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism

/-!
# Finite atlas subfamily covering a quasi-compact point of a formal algebraic space: refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcover`. A declaration of
that module whose statement the round strengthened keeps its original statement there; its
strengthened form lives here under a primed name.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite subfamily of a prescribed covering whose base changes cover a compact point.**
Let `X` be an fppf sheaf on the big fppf site of `S`, let `{Xᵢ ⟶ X}` be a covering as in
Definition **Stacks 0AIM** — the sources affine formal algebraic spaces, each arrow
representable by algebraic spaces and étale, the arrow out of the coproduct a surjection of
sheaves — and let `c : h_T ⟶ X` be a morphism from the universe-lifted Yoneda presheaf of an
object `T` of the big fppf category over `S` whose underlying space is compact. Then finitely
many members of the *given* covering already suffice: there are a finite type `K` and a
reindexing `k : K → I` for which the base changes of the members `X_{k j}` along `c` are
represented by objects `V j` of the site, are étale over `T`, and cover `T` on points.

Because the members keep their index in the given family, every datum carried by the original
covering restricts to the subfamily. That is what distinguishes this from producing a finite
covering by some other route, and it is what a refinement of a prescribed covering consumes.

Joint surjectivity of the full covering is the content of
`AlgebraicGeometry.FormalSpace.family_imageSieve_mem`; the base changes are objects of the site
by **Stacks 0AIG**; the images are open because the base changes are étale; and the subfamily is
finite because the space is compact. -/
theorem exists_finite_subfamily_pullback_cover_of_compactSpace {X : FppfSheaf B S hS}
    {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    {T : BigFppfOver B S hS}
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)]
    (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    ∃ (K : Type (u + 1)) (k : K → I) (V : K → BigFppfOver B S hS) (q : ∀ j, V j ⟶ T)
      (ξ : ∀ j, uliftYoneda.{u + 1}.obj (V j) ⟶ (Xi (k j)).obj),
      Finite K ∧
      (∀ j, IsPullback (ξ j) (uliftYoneda.{u + 1}.map (q j)) (f (k j)).hom c) ∧
      (∀ j, Etale ((BigFppfOver.toScheme B S hS).map (q j))) ∧
      ∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ j, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q j)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  -- Stacks 0AIG: every atlas arrow is representable by objects of the site
  have hrep : ∀ i, Y.relativelyRepresentable (f i).hom := by
    intro i
    obtain ⟨hfi, hetale⟩ := hf i
    exact relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS (f i) (hXi i) hfi hetale
  choose V q ξ hsq using fun i ↦ hrep i c
  -- étaleness of the atlas arrow after the represented base change along `c`
  have hetfst : ∀ i, Space.IsEtaleULift.{u + 1} B S hS (pullback.fst c (f i).hom) := by
    intro i
    obtain ⟨hfi, hetale⟩ := hf i
    exact hetale T c
  -- each `Vᵢ ⟶ T` is étale, the comparison isomorphism being absorbed
  have hq : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (q i)) := by
    intro i
    rw [← Space.isEtaleULift_uliftYoneda_map_iff.{u + 1, u} B S hS (q i)]
    intro U φ hφ
    rw [← (hsq i).flip.isoPullback_hom_fst, ← Category.assoc]
    refine hetfst i U (φ ≫ (hsq i).flip.isoPullback.hom) ?_
    exact ((P.relative Y).cancel_right_of_respectsIso φ _).mpr hφ
  -- every point of `T` is met by some member of the base-changed family
  have hpoint : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
    have hmem := family_imageSieve_mem J Xi X f hcover T (uliftYonedaEquiv c)
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨E, hE, hER⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hmem
    have hEF := B.isFppfCovering_of_isCovering hE
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
    intro x
    obtain ⟨j, y, hy⟩ := hEF.1 x
    let T₀ : C := Over.mk (E.f j ≫ T.hom)
    let b : T₀ ⟶ T := Over.homMk (E.f j)
    have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
    change (⨆ i, Presheaf.imageSieve (f i).hom (uliftYonedaEquiv c)) b at hb
    simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
    obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hb
    let m : Y.obj T₀ ⟶ (Xi i).obj := uliftYonedaEquiv.symm z
    have hw : m ≫ (f i).hom = Y.map b ≫ c := by
      apply uliftYonedaEquiv.injective
      rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} c b.op)
    let r : T₀ ⟶ V i := Y.preimage ((hsq i).lift m (Y.map b) hw)
    have hr : r ≫ q i = b := by
      apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage]
      exact (hsq i).lift_snd m (Y.map b) hw
    have hcomp : (BigFppfOver.toScheme B S hS).map r ≫
        (BigFppfOver.toScheme B S hS).map (q i) = (BigFppfOver.toScheme B S hS).map b := by
      rw [← Functor.map_comp, hr]
    refine ⟨i, (BigFppfOver.toScheme B S hS).map r y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hcomp]
    exact hy
  -- the images are open and the space is compact, so finitely many of them suffice
  have hOopen : ∀ i, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (q i))) := by
    intro i
    have := hq i
    exact (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map (q i))).isOpen_range
  have hOcover : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj T)) ⊆
      ⋃ i, Set.range ((BigFppfOver.toScheme B S hS).map (q i)) :=
    fun x _ ↦ Set.mem_iUnion.2 (hpoint x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ Set.range ((BigFppfOver.toScheme B S hS).map (q i))) hOopen hOcover
  refine ⟨{i : I // i ∈ s}, fun j ↦ j.1, fun j ↦ V j.1, fun j ↦ q j.1,
    fun j ↦ ξ j.1, inferInstance, fun j ↦ hsq j.1, fun j ↦ hq j.1, fun x ↦ ?_⟩
  have hx := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨i, hi, w, hw⟩ := hx
  exact ⟨⟨i, hi⟩, w, hw⟩

end AlgebraicGeometry.FormalSpace

end
