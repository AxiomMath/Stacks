module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.FrobeniusColimit
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardRefinement
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Standard fppf coverings on the big h category

On the underlying category of a big h site over `S`, with the fppf topology, the *standard fppf
coverings* of an object with affine underlying scheme are the finite families of morphisms of the
site from objects with affine underlying schemes whose underlying family of morphisms of schemes
is a standard fppf covering in the sense of Stacks 03X9: flat, of finite presentation and jointly
surjective. This file shows that they are covering families, that they are cofinal among the
fppf covering sieves of an object with affine underlying scheme (Stacks 03XA), and that their
iterated fibre products have affine underlying schemes. These are the hypotheses of the
Čech-vanishing criterion of Stacks 03F9 for the collection of affine objects.

## Main definitions

* `AlgebraicGeometry.BigHOver.IsStandardFppf`: a family of the site is a standard fppf covering
  of an object with affine underlying scheme.
* `AlgebraicGeometry.BigHOver.standardFppfHypercover`: the family of the site attached to a
  standard fppf covering of the underlying scheme of an object.

## Main results

* `AlgebraicGeometry.BigHOver.mem_fppfTopology_iff`: a sieve covers in the fppf topology exactly
  when it contains a family of the site whose underlying family is an fppf covering.
* `AlgebraicGeometry.BigHOver.IsStandardFppf.sieve₀_mem_fppfTopology`: a standard fppf covering
  generates a covering sieve.
* `AlgebraicGeometry.BigHOver.exists_isStandardFppf_sieve₀_le`: cofinality, Stacks 03XA.
* `AlgebraicGeometry.BigHOver.isAffine_toScheme_piObj`: the iterated fibre products of a family
  of affine objects over an affine object are affine.

## References

* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fppf precoverage is stable under composition -/

/-- If a presieve of the site is fppf, the presieve of the underlying morphisms of schemes of any
family generating it is an fppf covering. -/
theorem map_ofArrows_mem_fppfPrecoverage {ι : Type (u + 1)} {X₀ : BigHOver B S hS}
    {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ X₀)
    (hR : Presieve.ofArrows X f ∈ fppfPrecoverage B S hS X₀) :
    Presieve.ofArrows (fun i ↦ (BigHOver.toScheme B S hS).obj (X i))
        (fun i ↦ (BigHOver.toScheme B S hS).map (f i)) ∈
      Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj X₀) := by
  obtain ⟨E, hE, hEf⟩ := hR
  rw [PreZeroHypercover.presieve₀_map, hE, Presieve.map_ofArrows] at hEf
  exact hEf

/-- The fppf precoverage on the big h category over `S` is stable under composition. -/
instance fppfPrecoverage_isStableUnderComposition :
    (fppfPrecoverage B S hS).IsStableUnderComposition where
  comp_mem_coverings {ι} {X₀} {X} f hf {σ} {Y} g hg := by
    refine ⟨⟨Σ i, σ i, fun p ↦ Y _ p.2, fun p ↦ g _ _ ≫ f _⟩, rfl, ?_⟩
    have h := Precoverage.comp_mem_coverings (J := Scheme.fppfPrecoverage)
      (fun i ↦ (BigHOver.toScheme B S hS).map (f i))
      (map_ofArrows_mem_fppfPrecoverage B S hS f hf)
      (fun i j ↦ (BigHOver.toScheme B S hS).map (g i j))
      (fun i ↦ map_ofArrows_mem_fppfPrecoverage B S hS (g i) (hg i))
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map] using h

/-- An isomorphism of the site is an fppf covering by itself. -/
instance fppfPrecoverage_hasIsos : (fppfPrecoverage B S hS).HasIsos where
  mem_coverings_of_isIso {X Y} f _ := by
    refine ⟨⟨PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ f⟩, Presieve.ofArrows_pUnit _, ?_⟩
    have : IsIso ((BigHOver.toScheme B S hS).map f) := inferInstance
    have h := Scheme.Hom.singleton_mem_fppfPrecoverage ((BigHOver.toScheme B S hS).map f)
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map, Presieve.ofArrows_pUnit] using h

/-- **Covering sieves of the fppf topology.** A sieve of the big h category over `S` covers in the
fppf topology exactly when it contains the presieve of a family of the site whose underlying
family of morphisms of schemes is an fppf covering. -/
theorem mem_fppfTopology_iff {X : BigHOver B S hS} {R : Sieve X} :
    R ∈ fppfTopology B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj X) ∧ E.presieve₀ ≤ R.arrows := by
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨E, rfl, hE⟩, hle⟩
    exact ⟨E, hE, hle⟩
  · rintro ⟨E, hE, hle⟩
    exact ⟨_, ⟨E, rfl, hE⟩, hle⟩

/-! ### Standard fppf coverings -/

/-- An affine scheme locally of finite type over a scheme of the big h site is again in the
site. -/
theorem size_lt_cutoff_of_isAffine_of_locallyOfFiniteType {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hY : Y.size < B.cutoff) : X.size < B.cutoff := by
  have hcov : (⨆ _ : ULift.{u} Unit, (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens).1) = ⊤ := by
    ext x; simp
  have hI : Cardinal.mk (ULift.{u} Unit) ≤ Y.size ^ Cardinal.aleph0 :=
    calc
      Cardinal.mk (ULift.{u} Unit) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ Y.size := Scheme.aleph0_le_size _
      _ ≤ Y.size ^ Cardinal.aleph0 := Cardinal.self_le_power _ (by simp)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit f (fun _ => ⟨⊤, isAffineOpen_top X⟩) hcov hI hY

/-- **Standard fppf coverings of the site.** A family of morphisms of the big h category over
`S` with target an object with affine underlying scheme is a *standard fppf covering* when its
underlying family of morphisms of schemes is a standard fppf covering of Stacks 03X9: finitely
many affine sources, flat morphisms of finite presentation, jointly surjective. -/
def IsStandardFppf {U : BigHOver B S hS} (E : PreZeroHypercover.{u} U) : Prop :=
  ∃ _ : IsAffine ((BigHOver.toScheme B S hS).obj U),
    IsStandardCovering .fppf (fun i ↦ (BigHOver.toScheme B S hS).obj (E.X i))
      (fun i ↦ (BigHOver.toScheme B S hS).map (E.f i))

variable {B S hS}

/-- A standard fppf covering has finitely many members. -/
theorem IsStandardFppf.finite {U : BigHOver B S hS} {E : PreZeroHypercover.{u} U}
    (h : IsStandardFppf B S hS E) : Finite E.I₀ := by
  obtain ⟨_, h⟩ := h
  exact h.finite_index

/-- The target and the members of a standard fppf covering have affine underlying schemes. -/
theorem IsStandardFppf.isAffine {U : BigHOver B S hS} {E : PreZeroHypercover.{u} U}
    (h : IsStandardFppf B S hS E) :
    IsAffine ((BigHOver.toScheme B S hS).obj U) ∧
      ∀ i, IsAffine ((BigHOver.toScheme B S hS).obj (E.X i)) := by
  obtain ⟨hU, h⟩ := h
  exact ⟨hU, h.affine_source⟩

/-- **A standard fppf covering is a covering.** It generates a covering sieve of the fppf
topology. -/
theorem IsStandardFppf.sieve₀_mem_fppfTopology {U : BigHOver B S hS}
    {E : PreZeroHypercover.{u} U} (h : IsStandardFppf B S hS E) :
    E.sieve₀ ∈ fppfTopology B S hS U := by
  obtain ⟨hU, hstd⟩ := h
  let E' : PreZeroHypercover.{u + 1} U :=
    { I₀ := ULift.{u + 1} E.I₀, X i := E.X i.down, f i := E.f i.down }
  have hle : Sieve.generate E'.presieve₀ ≤ E.sieve₀ := by
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact Sieve.ofArrows_mk _ _ i.down
  have hmem : (E'.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj U) := by
    have h₁ := hstd.ofArrows_mem_precoverage .fppf _ _
    rw [Scheme.ofArrows_mem_precoverage_iff] at h₁
    show Presieve.ofArrows (fun i : ULift.{u + 1} E.I₀ ↦ (BigHOver.toScheme B S hS).obj
        (E.X i.down)) (fun i ↦ (BigHOver.toScheme B S hS).map (E.f i.down)) ∈
      Scheme.precoverage (coveringMorphismProperty .fppf) _
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ h₁.2 i.down⟩
    obtain ⟨i, hi⟩ := h₁.1 x
    exact ⟨ULift.up i, hi⟩
  exact (fppfTopology B S hS).superset_covering hle
    (Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hmem⟩)

variable (B S hS)

/-- The family of the site attached to a standard fppf covering of the scheme underlying an
object with affine underlying scheme. -/
def standardFppfHypercover {U : BigHOver B S hS}
    [IsAffine ((BigHOver.toScheme B S hS).obj U)] {I : Type u} {V : I → Scheme.{u}}
    {g : ∀ i, V i ⟶ (BigHOver.toScheme B S hS).obj U} (hg : IsStandardCovering .fppf V g) :
    PreZeroHypercover.{u} U where
  I₀ := I
  X i := Over.mk ((ObjectProperty.homMk (g i) :
    (B.obj (V i) (by
      have := hg.affine_source i
      have : Flat (g i) := (hg.standard i).1
      have : LocallyOfFinitePresentation (g i) := (hg.standard i).2.1
      exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType B (g i) U.left.property)) ⟶
        U.left) ≫ U.hom)
  f i := Over.homMk (ObjectProperty.homMk (g i)) (by simp)

/-- The family attached to a standard fppf covering is a standard fppf covering. -/
theorem isStandardFppf_standardFppfHypercover {U : BigHOver B S hS}
    [IsAffine ((BigHOver.toScheme B S hS).obj U)] {I : Type u} {V : I → Scheme.{u}}
    {g : ∀ i, V i ⟶ (BigHOver.toScheme B S hS).obj U} (hg : IsStandardCovering .fppf V g) :
    IsStandardFppf B S hS (standardFppfHypercover B S hS hg) :=
  ⟨inferInstance, hg⟩

variable {B S hS}

/-- **Cofinality of the standard fppf coverings, Stacks 03XA.** Every fppf covering sieve of an
object with affine underlying scheme contains a standard fppf covering. -/
theorem exists_isStandardFppf_sieve₀_le {U : BigHOver B S hS}
    (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) {R : Sieve U}
    (hR : R ∈ fppfTopology B S hS U) :
    ∃ E : PreZeroHypercover.{u} U, IsStandardFppf B S hS E ∧ E.sieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hER⟩ := (mem_fppfTopology_iff B S hS).mp hR
  obtain ⟨W, r, hW⟩ := exists_standardCovering_refinement .fppf
    (E.map (BigHOver.toScheme B S hS)) hE
  let := hW.finite_index
  let : Fintype W.I₀ := Fintype.ofFinite W.I₀
  let e : W.I₀ ≃ Fin (Fintype.card W.I₀) := Fintype.equivFin W.I₀
  let ix : ULift.{u} (Fin (Fintype.card W.I₀)) → W.I₀ := fun i => e.symm i.down
  have hW' : IsStandardCovering .fppf (fun i => W.X (ix i)) (fun i => W.f (ix i)) := by
    refine ⟨inferInstance, fun i => hW.affine_source (ix i), ?_,
      fun i => hW.standard (ix i)⟩
    refine Set.iUnion_eq_univ_iff.mpr fun x => ?_
    have hx : x ∈ ⋃ i, Set.range (W.f i) := by rw [hW.jointly_surjective]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine ⟨ULift.up (e i), ?_⟩
    rwa [show ix (ULift.up (e i)) = i from e.symm_apply_apply i]
  refine ⟨standardFppfHypercover B S hS hW', isStandardFppf_standardFppfHypercover B S hS hW', ?_⟩
  rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  let j : E.I₀ := r.s₀ (ix i)
  let a : (standardFppfHypercover B S hS hW').X i ⟶ E.X j :=
    Over.homMk (ObjectProperty.homMk (r.h₀ (ix i))) (by
      apply ObjectProperty.hom_ext
      have hw : r.h₀ (ix i) ≫ (E.f j).left.hom = W.f (ix i) := r.w₀ (ix i)
      have hEj : (E.X j).hom.hom = (E.f j).left.hom ≫ U.hom.hom := by
        rw [← Over.w (E.f j)]
        rfl
      show r.h₀ (ix i) ≫ (E.X j).hom.hom = W.f (ix i) ≫ U.hom.hom
      rw [hEj]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (Over.hom U).hom) hw))
  have hfac : a ≫ E.f j = (standardFppfHypercover B S hS hW').f i := by
    apply (BigHOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact r.w₀ (ix i)
  rw [← hfac]
  exact R.downward_closed (hER (E.X j) (E.f j) (Presieve.ofArrows.mk j)) a

/-- **Iterated fibre products of a family of affine objects over an affine object are affine.**
The underlying scheme of the product, in the slice of the site at `U`, of finitely many objects
with affine underlying schemes is affine. -/
theorem isAffine_toScheme_piObj {U : BigHOver B S hS}
    (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (E : PreZeroHypercover.{u} U)
    (hX : ∀ i, IsAffine ((BigHOver.toScheme B S hS).obj (E.X i))) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) :
    IsAffine ((BigHOver.toScheme B S hS).obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let v : BigHOver B S hS ⥤ Scheme.{u} := BigHOver.toScheme B S hS
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  let : IsAffine (v.obj U) := hU
  let : PreservesLimit (Discrete.functor A) (Over.post (X := U) v) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost v E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have hF : ∀ a, IsAffineHom ((Over.post (X := U) v).obj (A a)).hom := fun a ↦ by
    let : IsAffine ((Over.post (X := U) v).obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  let : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have haff : IsAffine (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).hom
  have e : v.obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ≅
      (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).left :=
    (Over.forget (v.obj U)).mapIso (PreservesProduct.iso (Over.post (X := U) v) A)
  exact IsAffine.of_isIso e.hom


end AlgebraicGeometry.BigHOver
