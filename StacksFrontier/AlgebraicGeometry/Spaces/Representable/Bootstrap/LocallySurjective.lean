module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Surjective flat morphisms locally of finite presentation are epimorphisms of sheaves

A morphism of presheaves on the big fppf site of a scheme `S` which is representable by
algebraic spaces, surjective, flat and locally of finite presentation is locally surjective
for the big fppf topology: every section of the target lifts to a section of the source
after passing to a covering.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 04S1**. The hypothesis naming the statement is representability: the morphism is one
  of presheaves, and surjectivity, flatness and local finite presentation are asked of its
  charts. For a morphism whose source and target are themselves algebraic spaces the statement
  is `AlgebraicGeometry.Space.isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation`
  in `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings`.

## Implementation notes

Let `x` be a section of `G` over an object `U` of the site, let `ξ : h_U ⟶ G` be the
corresponding morphism, and let `P = h_U ×_G F` with first projection `p`.  By
representability `P` is an algebraic space over `S`, and `p` is surjective, flat and locally
of finite presentation because `a` is.  A surjective étale scheme atlas `φ : h_V ⟶ P`
therefore produces a single morphism `j : V ⟶ U` of the site, namely the preimage of
`φ ≫ p` under the fully faithful Yoneda embedding, whose underlying morphism of schemes is
surjective, flat and locally of finite presentation — surjective because `|φ|` and `|p|` are
both surjective, and flat and locally of finite presentation because the square of étale
charts `(φ, 𝟙_{h_U})` over `p` has `j` as its underlying morphism.  So `j` alone is an fppf
covering of `U`, and `x` lifts over it: the section of `F` obtained from
`φ ≫ pr_F : h_V ⟶ F` at the identity of `V` maps to the restriction of `x` along `j`.

Being a covering *of the site* is a stronger requirement than generating an fppf covering
sieve, because the site is closed under neither arbitrary coproducts nor arbitrary base
change; `AlgebraicGeometry.exists_isCovering_refining_fppfCovering` provides a covering of
the site refining the one-member family `{j}`, and the image sieve of `x` under `a`, which
is downward closed and contains `j`, therefore contains that covering.

The chart of `h_U` used above is the identity, whose representable étaleness is
`AlgebraicGeometry.presheaf_id_of_iso`; no auxiliary statement about identities is needed.

The two sheaf hypotheses are those of the source statement and are kept, but the argument
above does not use them: the conclusion holds for arbitrary presheaves `F` and `G`.

## References

* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04S1.** A morphism of fppf sheaves on the big fppf site of `S` which is
representable by algebraic spaces, surjective, flat and locally of finite presentation is
locally surjective for the big fppf topology. -/
@[stacks 04S1]
theorem isLocallySurjective_of_isRepresentableByAlgebraicSpaces
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (_hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hflat : HasProperty B S hS (fun _ _ f => IsFlat B S hS f.hom) a ha)
    (hlfp : HasProperty B S hS
      (fun _ _ f => IsLocallyOfFinitePresentation B S hS f.hom) a ha)
    (hsurj : HasProperty B S hS (fun _ _ f => IsSurjective B S hS f.hom) a ha) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  classical
  let J := BigFppfOver.topology B S hS
  let Tscheme := BigFppfOver.toScheme B S hS
  refine ⟨fun {U} x => ?_⟩
  let ξ : yoneda.obj U ⟶ G := yonedaEquiv.symm x
  let p := pullback.fst ξ a
  have hP : IsAlgebraicSpace B S hS (pullback ξ a) := ha U ξ
  -- A surjective étale scheme atlas of the fibre product.
  obtain ⟨V, φ, hφs, hφe⟩ := hP.exists_atlas
  have hidEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf
      (𝟙 (yoneda.obj U)) :=
    presheaf_id_of_iso B S hS _ (fun _ _ f hf => by
      have := hf
      change Etale (Tscheme.map f)
      infer_instance) U
  -- The single morphism of the site through which `x` is lifted.
  let j : V ⟶ U := yoneda.preimage (φ ≫ p)
  have hjmap : yoneda.map j = φ ≫ p := yoneda.map_preimage _
  have hchart : yoneda.map j ≫ 𝟙 (yoneda.obj U) = φ ≫ p := (Category.comp_id _).trans hjmap
  have hjflat : Flat (Tscheme.map j) :=
    hflat U ξ V U φ (𝟙 (yoneda.obj U)) j hφe hidEtale hchart
  have hjlfp : LocallyOfFinitePresentation (Tscheme.map j) :=
    hlfp U ξ V U φ (𝟙 (yoneda.obj U)) j hφe hidEtale hchart
  have hjSurjPsh : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf (yoneda.map j) := by
    refine (surjective_yonedaMap_iff_surjective_pointsMap B S hS j).mpr ?_
    rw [hjmap, pointsMap_comp]
    exact (hsurj U ξ).comp
      ((surjective_iff_surjective_pointsMap B S hS _ hP V φ).mp hφs)
  have hjSurj : Surjective (Tscheme.map j) := by
    apply hjSurjPsh.2 (𝟙 _) (𝟙 _) j
    simpa using (IsPullback.of_id_fst (f := yoneda.map j))
  -- `x` lifts over `j`.
  have hjR : (Presheaf.imageSieve a x) j := by
    rw [Presheaf.imageSieve_apply]
    refine ⟨(φ ≫ pullback.snd ξ a).app (op V) (𝟙 V), ?_⟩
    have h : (φ ≫ pullback.snd ξ a) ≫ a = yoneda.map j ≫ ξ := by
      rw [hjmap, Category.assoc, ← pullback.condition, Category.assoc]
    simpa [ξ] using congrArg (fun f => f.app (op V) (𝟙 V)) h
  -- `{j}` is an fppf covering of `U`, so it is refined by a covering of the site.
  let E : PreZeroHypercover.{u + 1} (B.inclusion.obj U.left) :=
    PreZeroHypercover.singleton (B.inclusion.map ((BigFppfOver.forget B S hS).map j))
  have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    have _ : Flat (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjflat
    have _ : Surjective (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjSurj
    have _ : LocallyOfFinitePresentation
      (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjlfp
    simpa [E, PreZeroHypercover.presieve₀_singleton] using
      (B.inclusion.map ((BigFppfOver.forget B S hS).map j)).singleton_mem_fppfPrecoverage
  obtain ⟨E', hE', ⟨ρ⟩⟩ := exists_isCovering_refining_fppfCovering B U.left E hE
  let R := Presheaf.imageSieve a x
  have hRcov : (Sieve.overEquiv U).symm E'.sieve₀ ∈ J U := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
      (Precoverage.generate_mem_toGrothendieck
        (show E'.presieve₀ ∈ B.precoverage U.left from ⟨E', rfl, hE'⟩))
  have hle : (Sieve.overEquiv U).symm E'.sieve₀ ≤ R := by
    rw [← ((Sieve.overEquiv U).symm).apply_symm_apply R,
      ((Sieve.overEquiv U).symm).map_rel_iff]
    simp only [OrderIso.symm_symm]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    change (Sieve.overEquiv U (Presheaf.imageSieve a x)).arrows (E'.f i)
    rw [Sieve.overEquiv_iff]
    let α : Over.mk (E'.f i ≫ U.hom) ⟶ U := Over.homMk (E'.f i) (by simp)
    let b : (Over.mk (E'.f i ≫ U.hom)).left ⟶ (BigFppfOver.forget B S hS).obj V :=
      B.inclusion.preimage (ρ.h₀ i)
    have hbmap : B.inclusion.map b = ρ.h₀ i := B.inclusion.map_preimage _
    have href0 : ρ.h₀ i ≫ B.inclusion.map ((BigFppfOver.forget B S hS).map j) =
        B.inclusion.map (E'.f i) := by
      simpa [E, PreZeroHypercover.singleton] using ρ.w₀ i
    have hbp : b ≫ (BigFppfOver.forget B S hS).map j = E'.f i :=
      B.inclusion.map_injective (by rwa [B.inclusion.map_comp, hbmap])
    let β : Over.mk (E'.f i ≫ U.hom) ⟶ V := Over.homMk b (by
      rw [← Over.w j, ← Category.assoc]
      exact congrArg (· ≫ U.hom) hbp)
    change R α
    rw [← show β ≫ j = α from Over.OverMorphism.ext hbp]
    exact R.downward_closed hjR β
  exact J.superset_covering hle hRcov

end AlgebraicGeometry.Space

end
