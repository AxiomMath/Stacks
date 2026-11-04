module

public import Mathlib.Algebra.Ring.ULift
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallWeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleCovers
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationFromWeaklyContractibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.Over
import StacksCore.Tactic.StacksAttribute

/-!
# Compact generation of the derived category of the big pro-étale site

The derived category of sheaves of modules over a sheaf of rings on the big pro-étale site of a
scheme is compactly generated, and so is the one of the small pro-étale site. The generating
objects are the free modules on the affine objects with w-contractible ring of global sections.

## Main results

* `CategoryTheory.GrothendieckTopology.isQuasiCompactObject_of_finite_refinements`: an object
  all of whose covering sieves are refined by a finite family is a quasi-compact object.
* `AlgebraicGeometry.ProEtale.BigProetaleOver.exists_clopenRefinement_of_isWContractible`: the
  refinement statement of Stacks 098H in the big pro-étale site of a scheme.
* `AlgebraicGeometry.ProEtale.BigProetaleOver.isQuasiCompactObject_of_isWContractible` and
  `AlgebraicGeometry.ProEtale.BigProetaleOver.surjective_sections_of_isWContractible`: the two
  consequences.
* `AlgebraicGeometry.ProEtale.BigProetaleOver.hasEnoughObjects_isAffine_isWContractible`:
  **Stacks 098I** in the big pro-étale site of a scheme.
* `AlgebraicGeometry.ProEtale.isCompactlyGenerated_derivedCategory_bigProetaleOver`:
  **Stacks 0F4Q, clause (6)**.

## Implementation notes

The objects of the big pro-étale site of `S` lie in `Type (u + 1)` while its morphisms lie in
`Type u`, so sheaves of modules on it have their sections in `Type (u + 1)`, and the sheaf of
rings is taken in `RingCat.{u + 1}` accordingly.

## References

* [Stacks Project, Tag 0F4Q](https://stacks.math.columbia.edu/tag/0F4Q)
* [Stacks Project, Tag 098I](https://stacks.math.columbia.edu/tag/098I)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

namespace CategoryTheory.GrothendieckTopology

universe v u

/-- **An object all of whose coverings are refined by a finite family is quasi-compact**
(Stacks 090H). -/
theorem isQuasiCompactObject_of_finite_refinements {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i)) :
    J.IsQuasiCompactObject U := by
  classical
  intro 𝒰 h𝒰
  obtain ⟨n, V, f, hcov, hmem⟩ := href 𝒰.sieve₀ h𝒰
  choose j a ha using fun i ↦ (Sieve.mem_ofArrows_iff 𝒰.X 𝒰.f (f i)).1 (hmem i)
  refine ⟨{ I₀ := ULift.{max u v} (Fin n)
            X := fun i ↦ V i.down
            f := fun i ↦ f i.down },
    { s₀ := fun i ↦ j i.down
      h₀ := fun i ↦ a i.down
      w₀ := fun i ↦ (ha i.down).symm }, ?_, ?_⟩
  · have heq : Sieve.ofArrows (fun i : ULift.{max u v} (Fin n) ↦ V i.down)
        (fun i ↦ f i.down) = Sieve.ofArrows V f := Sieve.ext fun W g ↦ by
      rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
      exact ⟨fun ⟨i, b, hb⟩ ↦ ⟨i.down, b, hb⟩, fun ⟨i, b, hb⟩ ↦ ⟨ULift.up i, b, hb⟩⟩
    show Sieve.ofArrows (fun i : ULift.{max u v} (Fin n) ↦ V i.down) (fun i ↦ f i.down) ∈ J U
    rwa [heq]
  · exact Set.finite_range _

/-- A refinement of every covering sieve by a finite family that is itself covering, with extra
properties, shows that an object is quasi-compact. -/
private theorem isQuasiCompactObject_of_refinements {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) {P : ∀ {n : ℕ} (V : Fin n → C), (∀ i, V i ⟶ U) → Prop}
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        P V f ∧ Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i)) :
    J.IsQuasiCompactObject U :=
  isQuasiCompactObject_of_finite_refinements J U fun S hS ↦
    let ⟨n, V, f, _, h⟩ := href S hS
    ⟨n, V, f, h⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.ProEtale

universe u

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BigProetaleOver

/-- The empty sieve covers an object of the big pro-étale site of `S` whose underlying scheme
has empty space. -/
private theorem bot_mem_topology_of_isEmpty (Z : BigProetaleOver B S hS)
    (hZ : IsEmpty ((toScheme B S hS).obj Z).carrier) :
    (⊥ : Sieve Z) ∈ topology B S hS Z := by
  rw [GrothendieckTopology.mem_over_iff, map_bot]
  exact B.bot_mem_topology_of_isEmpty Z.left hZ

/-- A morphism of the big pro-étale site of `S` which is a monomorphism of schemes is a
monomorphism of the site. -/
private theorem mono_of_mono_map {X Y : BigProetaleOver B S hS} (f : X ⟶ Y)
    (hf : Mono ((toScheme B S hS).map f)) : Mono f :=
  (Over.forget _).mono_of_mono_map (B.inclusion.mono_of_mono_map hf)

/-- **Stacks 098H, (1) implies (3), in the big pro-étale site of `S`.** Every covering sieve of
an object whose underlying scheme is affine with w-contractible ring of global sections is
refined by a finite family of objects of the site whose images form a disjoint clopen cover. -/
theorem exists_clopenRefinement_of_isWContractible (T : BigProetaleOver B S hS)
    (hA : IsAffine ((toScheme B S hS).obj T))
    (hW : IsWContractible.{u, u} Γ((toScheme B S hS).obj T, ⊤))
    (Sv : Sieve T) (hSv : Sv ∈ topology B S hS T) :
    ∃ (n : ℕ) (V : Fin n → BigProetaleOver B S hS) (f : (i : Fin n) → V i ⟶ T),
      IsClopenDecompositionCover (fun i ↦ (toScheme B S hS).obj (V i))
          (fun i ↦ (toScheme B S hS).map (f i)) ∧
        Sieve.ofArrows V f ∈ topology B S hS T ∧ ∀ i, Sv.arrows (f i) := by
  have : IsAffine T.left.obj := hA
  obtain ⟨n, U, g, hdec, hmem⟩ := ProEtale.exists_clopenRefinement_of_isWContractible B T.left
    hW _ ((GrothendieckTopology.mem_over_iff B.topology Sv).1 hSv)
  refine ⟨n, fun i ↦ Over.mk (g i ≫ T.hom), fun i ↦ Over.homMk (g i), hdec, ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact B.sieve_ofArrows_mem_topology_of_isClopenDecompositionCover T.left U g hdec
  · exact fun i ↦ (Sieve.overEquiv_iff Sv (g i)).1 (hmem i)

/-- **An affine object with w-contractible ring of global sections is a quasi-compact object of
the big pro-étale site of `S`** (Stacks 090H). -/
theorem isQuasiCompactObject_of_isWContractible (T : BigProetaleOver B S hS)
    (hA : IsAffine ((toScheme B S hS).obj T))
    (hW : IsWContractible.{u, u} Γ((toScheme B S hS).obj T, ⊤)) :
    (topology B S hS).IsQuasiCompactObject T :=
  GrothendieckTopology.isQuasiCompactObject_of_refinements _ T fun Sv hSv ↦
    exists_clopenRefinement_of_isWContractible B S hS T hA hW Sv hSv

/-- **An affine object with w-contractible ring of global sections tests surjectivity of
morphisms of sheaves of sets on the big pro-étale site of `S`**, in any universe of values: a
locally surjective morphism is surjective on sections over such an object. -/
theorem surjective_sections_of_isWContractible (T : BigProetaleOver B S hS)
    (hA : IsAffine ((toScheme B S hS).obj T))
    (hW : IsWContractible.{u, u} Γ((toScheme B S hS).obj T, ⊤))
    (F G : Sheaf (topology B S hS) (Type (u + 1))) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op T)) :=
  GrothendieckTopology.surjective_sections_of_clopenRefinements (topology B S hS)
    (toScheme B S hS) T (bot_mem_topology_of_isEmpty B S hS)
    (fun f hf ↦ mono_of_mono_map B S hS f hf)
    (fun Sv hSv ↦ exists_clopenRefinement_of_isWContractible B S hS T hA hW Sv hSv)
    F G φ hφ

/-- **An affine object with w-contractible ring of global sections is weakly contractible in
the big pro-étale site of `S`** (Stacks 090L (1)). -/
theorem isWeaklyContractible_of_isWContractible (T : BigProetaleOver B S hS)
    (hA : IsAffine ((toScheme B S hS).obj T))
    (hW : IsWContractible.{u, u} Γ((toScheme B S hS).obj T, ⊤)) :
    (topology B S hS).IsWeaklyContractible T :=
  GrothendieckTopology.isWeaklyContractible_of_clopenRefinements (topology B S hS)
    (toScheme B S hS) T (bot_mem_topology_of_isEmpty B S hS)
    (fun f hf ↦ mono_of_mono_map B S hS f hf)
    (fun Sv hSv ↦ exists_clopenRefinement_of_isWContractible B S hS T hA hW Sv hSv)

/-- Every object of the big pro-étale site of `S` is covered by objects whose underlying schemes
are affine with w-contractible ring of global sections. -/
@[stacks 098I "in the big pro-étale site of a scheme"]
theorem hasEnoughObjects_isAffine_isWContractible (T : BigProetaleOver B S hS) :
    ∃ (I : Type (u + 1)) (V : I → BigProetaleOver B S hS) (p : (i : I) → V i ⟶ T),
      Sieve.ofArrows V p ∈ topology B S hS T ∧
        ∀ i, IsAffine ((toScheme B S hS).obj (V i)) ∧
          IsWContractible.{u, u} Γ((toScheme B S hS).obj (V i), ⊤) := by
  obtain ⟨E, hE, hprop⟩ := ProEtale.exists_covering_affine_wContractible B T.left
  refine ⟨E.I₀, fun i ↦ Over.mk (E.f i ≫ T.hom), fun i ↦ Over.homMk (E.f i), ?_,
    fun i ↦ ⟨(hprop i).1, (hprop i).2.1⟩⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩

end BigProetaleOver

namespace SmallProetale

/-- **Stacks 098H, (1) implies (3), in the small pro-étale site of `S`.** Every covering sieve
of an affine object of the small pro-étale site whose ring of global sections is w-contractible
is refined by a finite family of objects of the site whose images form a disjoint clopen cover. -/
theorem exists_clopenRefinement_of_isWContractible (U : SmallProetale B S hS)
    (hA : IsAffine U.obj.left.obj)
    (hW : IsWContractible.{u, u} Γ(U.obj.left.obj, ⊤))
    (Sv : Sieve U) (hSv : Sv ∈ topology B S hS U) :
    ∃ (n : ℕ) (V : Fin n → SmallProetale B S hS) (f : (i : Fin n) → V i ⟶ U),
      IsClopenDecompositionCover (fun i ↦ (toScheme B S hS).obj (V i))
          (fun i ↦ (toScheme B S hS).map (f i)) ∧
        Sieve.ofArrows V f ∈ topology B S hS U ∧ ∀ i, Sv.arrows (f i) := by
  classical
  have : IsAffine U.obj.left.obj := hA
  let I := inclusion B S hS
  let q := BigProetaleOver.forget B S hS
  let Q := I ⋙ q
  let J := topology B S hS
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨E, hE, hET⟩ := exists_covering_le_of_isSite (IsCovering B S hS)
    (isSite B S hS) (precoverage B S hS) (fun _ _ ↦ Iff.rfl) Sv hSv
  have hT' : Sv.functorPushforward Q ∈ B.topology (Q.obj U) := by
    refine B.topology.superset_covering (Sieve.functorPushforward_monotone Q U
      ((Sieve.generate_le_iff _ _).mpr hET)) ?_
    rw [← PreZeroHypercover.sieve₀_map]
    exact Precoverage.generate_mem_toGrothendieck ⟨E.map Q, rfl, hE⟩
  obtain ⟨n, V, g, hdec, href⟩ :=
    ProEtale.exists_clopenRefinement_of_isWContractible B U.obj.left hW _ hT'
  have hwe (i : Fin n) : WeaklyEtale (B.inclusion.map (g i ≫ U.obj.hom)) := by
    have h₁ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
    have h₂ : WeaklyEtale (B.inclusion.map U.obj.hom) := U.property
    rw [B.inclusion.map_comp]; infer_instance
  let X (i : Fin n) : SmallProetale B S hS := ⟨Over.mk (g i ≫ U.obj.hom), hwe i⟩
  let f (i : Fin n) : X i ⟶ U := I.preimage (Over.homMk (g i))
  have hQp {Y Z : SmallProetale B S hS} (h : I.obj Y ⟶ I.obj Z) :
      Q.map (I.preimage h) = h.left := by
    dsimp only [Q, Functor.comp_map]; rw [Functor.map_preimage]; rfl
  have hQf (i : Fin n) : Q.map (f i) = g i := hQp _
  let F : PreZeroHypercover.{u + 1} U :=
    ⟨ULift.{u + 1} (Fin n), fun i ↦ X i.down, fun i ↦ f i.down⟩
  have hF : B.IsProetaleCovering ⟨Q.obj U, F.map Q⟩ := by
    show ((F.map Q).map B.inclusion).presieve₀ ∈ _
    apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
    rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (g i)).base :=
        (Set.ext_iff.mp hdec.cover x).mpr (Set.mem_univ x)
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
      refine ⟨ULift.up i, y, ?_⟩
      show (B.inclusion.map (Q.map (f i))).base y = x
      rwa [hQf]
    · show IsOpenImmersion (B.inclusion.map (Q.map (f i.down)))
      rw [hQf]; exact hdec.openImmersion i.down
  have hFQfin : Finite (F.map Q).I₀ := inferInstanceAs (Finite (ULift.{u + 1} (Fin n)))
  obtain ⟨ι, hfin, a, ha, -⟩ := B.exists_finite_restrictIndex_covering (F.map Q) hF
  have hFa : (F.restrictIndex a).sieve₀ ∈ J U :=
    Precoverage.generate_mem_toGrothendieck ⟨F.restrictIndex a, rfl, ha⟩
  have hFtop : F.sieve₀ ∈ J U :=
    J.superset_covering (Sieve.generate_mono (F.presieve₀_restrictIndex_le a)) hFa
  have hcover : Sieve.ofArrows X f ∈ J U := by
    refine J.superset_covering (fun Y b hb ↦ ?_) hFtop
    obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hb
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i.down, c, hc⟩
  refine ⟨n, X, f, ?_, hcover, fun i ↦ ?_⟩
  · show IsClopenDecompositionCover (fun i ↦ (V i).obj)
      (fun i ↦ B.inclusion.map (Q.map (f i)))
    simpa only [hQf] using hdec
  · obtain ⟨Z, c₁, c₂, hc₁, hc₂⟩ := href i
    let c : X i ⟶ Z := I.preimage (Over.homMk c₂ (by
      have hw : Q.map c₁ ≫ U.obj.hom = Z.obj.hom := Over.w (I.map c₁)
      show c₂ ≫ Z.obj.hom = g i ≫ U.obj.hom
      rw [← hw, ← Category.assoc, ← hc₂]))
    have hc : c ≫ c₁ = f i := by
      refine I.map_injective (q.map_injective ?_)
      show Q.map c ≫ Q.map c₁ = Q.map (f i)
      rw [hQf, hQp]
      exact hc₂.symm
    exact hc ▸ Sv.downward_closed hc₁ c

/-- **An affine object with w-contractible ring of global sections is a quasi-compact object of
the small pro-étale site of `S`** (Stacks 090H). -/
theorem isQuasiCompactObject_of_isWContractible (U : SmallProetale B S hS)
    (hA : IsAffine U.obj.left.obj)
    (hW : IsWContractible.{u, u} Γ(U.obj.left.obj, ⊤)) :
    (topology B S hS).IsQuasiCompactObject U :=
  GrothendieckTopology.isQuasiCompactObject_of_refinements _ U fun Sv hSv ↦
    exists_clopenRefinement_of_isWContractible B S hS U hA hW Sv hSv

/-- **An affine object with w-contractible ring of global sections is weakly contractible in the
small pro-étale site of `S`** (Stacks 090L (1)). -/
theorem isWeaklyContractible_of_isWContractible (U : SmallProetale B S hS)
    (hA : IsAffine U.obj.left.obj)
    (hW : IsWContractible.{u, u} Γ(U.obj.left.obj, ⊤)) :
    (topology B S hS).IsWeaklyContractible U := by
  have : IsAffine U.obj.left.obj := hA
  intro F G φ hφ
  exact surjective_sections_of_isWContractible B S hS U hW F G φ hφ

/-- Abelian sheaves on the small pro-étale site of `S`, with sections in the universe of its
objects, admit sheafification. -/
instance hasSheafify_smallProetale :
    HasSheafify (topology B S hS) AddCommGrpCat.{u + 1} :=
  smallProetale_hasSheafify B ⟨S, hS⟩

/-- Sheafification of abelian sheaves on the small pro-étale site of `S`, with sections in the
universe of its objects, inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_smallProetale :
    (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}

end SmallProetale

/-- Abelian sheaves on the big pro-étale site of `S`, with sections in the universe of its
objects, admit sheafification. -/
instance hasSheafify_bigProetaleOver :
    HasSheafify (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1} :=
  bigProetaleOver_hasSheafify B ⟨S, hS⟩

/-- Sheafification of abelian sheaves on the big pro-étale site of `S`, with sections in the
universe of its objects, inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_bigProetaleOver :
    (BigProetaleOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}

attribute [local instance] HasDerivedCategory.standard

/- The cohomology imports provide a second route to the abelian structure on sheaves of
modules, stated at a universe written as an iterated maximum; its unification against the
single universe of the statement below has no unique solution.  Pinning the direct route with a
higher priority is what makes the statement elaborate. -/
attribute [local instance 1100] _root_.AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules

/-- For a sheaf of rings `𝒜` on the big pro-étale site of a scheme `S`, the unbounded derived
category of sheaves of `𝒜`-modules is compactly generated. -/
@[stacks 0F4Q "clause (6): the derived category of sheaves of modules over a sheaf of rings \
  on the big pro-étale site (Sch/S)_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_bigProetaleOver
    (𝒜 : Sheaf (BigProetaleOver.topology B S hS) RingCat.{u + 1}) :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (SheafOfModules.{u + 1} 𝒜)) :=
  Stacks.Cohomology.isCompactlyGenerated_derivedCategory_of_hasEnoughObjects.{u + 1, u + 1, u, 0}
    (BigProetaleOver.topology B S hS) 𝒜
    (fun W ↦ IsAffine ((BigProetaleOver.toScheme B S hS).obj W) ∧
      IsWContractible.{u, u} Γ((BigProetaleOver.toScheme B S hS).obj W, ⊤))
    (fun W hW ↦ BigProetaleOver.isQuasiCompactObject_of_isWContractible B S hS W hW.1 hW.2)
    (fun W hW ↦ BigProetaleOver.surjective_sections_of_isWContractible B S hS W hW.1 hW.2)
    (BigProetaleOver.hasEnoughObjects_isAffine_isWContractible B S hS)

/-- Presheaves of rings on the big pro-étale site of `S`, with sections in the universe of its
objects, admit sheafification. -/
instance hasSheafify_ringCat_bigProetaleOver :
    HasSheafify (BigProetaleOver.topology B S hS) RingCat.{u + 1} :=
  Stacks.Cohomology.hasSheafify_ringCat.{u + 1, u + 1, u} _

/-- Sheafification of presheaves of rings on the big pro-étale site of `S`, with sections in
the universe of its objects, inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_ringCat_bigProetaleOver :
    (BigProetaleOver.topology B S hS).WEqualsLocallyBijective RingCat.{u + 1} :=
  Stacks.Cohomology.wEqualsLocallyBijective_ringCat.{u + 1, u + 1, u} _

/-- Presheaves of rings on the small pro-étale site of `S`, with sections in the universe of
its objects, admit sheafification. -/
instance hasSheafify_ringCat_smallProetale :
    HasSheafify (SmallProetale.topology B S hS) RingCat.{u + 1} :=
  Stacks.Cohomology.hasSheafify_ringCat.{u + 1, u + 1, u} _

/-- Sheafification of presheaves of rings on the small pro-étale site of `S`, with sections in
the universe of its objects, inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_ringCat_smallProetale :
    (SmallProetale.topology B S hS).WEqualsLocallyBijective RingCat.{u + 1} :=
  Stacks.Cohomology.wEqualsLocallyBijective_ringCat.{u + 1, u + 1, u} _

/-- The unbounded derived category of abelian sheaves on the big pro-étale site of a scheme `S`
is compactly generated. -/
@[stacks 0F4Q "clause (4): the derived category of abelian sheaves on the big pro-étale site \
  (Sch/S)_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_bigProetaleOver_abelian :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1})) :=
  Stacks.Cohomology.isCompactlyGenerated_derivedCategory_abelianSheaves_of_hasEnoughObjects.{u + 1,
      u + 1, u, 0}
    (BigProetaleOver.topology B S hS)
    (fun W ↦ IsAffine ((BigProetaleOver.toScheme B S hS).obj W) ∧
      IsWContractible.{u, u} Γ((BigProetaleOver.toScheme B S hS).obj W, ⊤))
    (fun W hW ↦ BigProetaleOver.isQuasiCompactObject_of_isWContractible B S hS W hW.1 hW.2)
    (fun W hW ↦ BigProetaleOver.surjective_sections_of_isWContractible B S hS W hW.1 hW.2)
    (BigProetaleOver.hasEnoughObjects_isAffine_isWContractible B S hS)

/-- For a ring `Λ`, the unbounded derived category of sheaves of `Λ`-modules on the big
pro-étale site of a scheme `S`, the sheaves of modules over the constant sheaf of rings with
value `Λ`, is compactly generated. -/
@[stacks 0F4Q "clause (5): the derived category of sheaves of Λ-modules, for a ring Λ, on the \
  big pro-étale site (Sch/S)_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_bigProetaleOver_constant (Λ : Type u) [Ring Λ] :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (SheafOfModules.{u + 1}
        ((constantSheaf (BigProetaleOver.topology B S hS) RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} Λ))))) :=
  isCompactlyGenerated_derivedCategory_bigProetaleOver B S hS _

/-- For a sheaf of rings `𝒜` on the small pro-étale site of a scheme `S`, the unbounded derived
category of sheaves of `𝒜`-modules is compactly generated. -/
@[stacks 0F4Q "clause (3): the derived category of sheaves of modules over a sheaf of rings \
  on the small pro-étale site S_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_smallProetale
    (𝒜 : Sheaf (SmallProetale.topology B S hS) RingCat.{u + 1}) :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (SheafOfModules.{u + 1} 𝒜)) :=
  Stacks.Cohomology.isCompactlyGenerated_derivedCategory_of_hasEnoughObjects.{u, u + 1, u, 0}
    (SmallProetale.topology B S hS) 𝒜
    (SmallProetale.IsWContractibleObject B S hS)
    (fun W hW ↦ SmallProetale.isQuasiCompactObject_of_isWContractible B S hS W hW.1 hW.2)
    (fun W hW ↦
      have _ : IsAffine W.obj.left.obj := hW.1
      SmallProetale.surjective_sections_of_isWContractible.{u + 1} B S hS W hW.2)
    (SmallProetale.hasEnoughObjects_isWContractible B ⟨S, hS⟩)

/-- For a ring `Λ`, the unbounded derived category of sheaves of `Λ`-modules on the small
pro-étale site of a scheme `S`, the sheaves of modules over the constant sheaf of rings with
value `Λ`, is compactly generated. -/
@[stacks 0F4Q "clause (2): the derived category of sheaves of Λ-modules, for a ring Λ, on the \
  small pro-étale site S_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_smallProetale_constant (Λ : Type u) [Ring Λ] :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (SheafOfModules.{u + 1}
        ((constantSheaf (SmallProetale.topology B S hS) RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} Λ))))) :=
  isCompactlyGenerated_derivedCategory_smallProetale B S hS _

/-- The unbounded derived category of abelian sheaves on the small pro-étale site of a scheme
`S` is compactly generated. -/
@[stacks 0F4Q "clause (1): the derived category of abelian sheaves on the small pro-étale \
  site S_proétale of a scheme S in a chosen big pro-étale site"]
theorem isCompactlyGenerated_derivedCategory_smallProetale_abelian :
    Pretriangulated.IsCompactlyGenerated.{u + 1}
      (DerivedCategory (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1})) :=
  Stacks.Cohomology.isCompactlyGenerated_derivedCategory_abelianSheaves_of_hasEnoughObjects.{u,
      u + 1, u, 0}
    (SmallProetale.topology B S hS)
    (SmallProetale.IsWContractibleObject B S hS)
    (fun W hW ↦ SmallProetale.isQuasiCompactObject_of_isWContractible B S hS W hW.1 hW.2)
    (fun W hW ↦
      have _ : IsAffine W.obj.left.obj := hW.1
      SmallProetale.surjective_sections_of_isWContractible.{u + 1} B S hS W hW.2)
    (SmallProetale.hasEnoughObjects_isWContractible B ⟨S, hS⟩)

end AlgebraicGeometry.ProEtale

end
