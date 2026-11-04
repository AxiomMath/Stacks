module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleLocalOnSource
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactObjects

/-!
# Representable étaleness over a directed colimit, tested on quasi-compact objects

Let `S` be a scheme contained in a big fppf site `B`. A morphism `ζ : X ⟶ Z` of fppf sheaves
over `S` which becomes representable étale after base change along a family of morphisms
`ψ i : W i ⟶ Z` is representable étale as soon as every scheme-valued point of `Z` factors
through a member of the family; that is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`, and it is the step by
which the charts of a directed colimit are seen to be étale over it.

Its factorization hypothesis is **false** when the test object is allowed to be an arbitrary
object of the site: for `Λ = ℕ`, `E n` the sheaf of `Spec k[t]/tⁿ` and `Z = Spf k[[t]]` the
colimit, the point of `Z` over `U = ∐ₙ Spec k[t]/tⁿ` whose `n`-th component is `colimit.ι E n`
factors through no stage; the argument is written out in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces`. What is true, and what
the source of Stacks 0GVN actually uses, is the factorization of a point out of a
*quasi-compact* object, and that is a theorem:
`CategoryTheory.Sheaf`-level, it is
`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`.

This file bridges the gap between the two. The **étale** half of representable étaleness is
Zariski local on the test object, with no set-theoretic side condition at all: that is
`AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_of_affine`, and it reduces the étale
clause at an arbitrary object of the site to the étale clause at its affine opens, which are
quasi-compact. The **representability** half is not local in this way — the atlases of the base
changes over the affine opens of a point have to be assembled into one object of the site, and
that needs a uniform bound on their sizes below the site's cutoff, which étaleness alone does
not supply (`∐_κ T` is étale over `T` for every `κ`). It is therefore the hypothesis `hrep` of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_compact_stageSquares`, which is the
set-theoretic residue of the argument and is implied by the conclusion.

## Main results

* `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_of_affine`: étaleness of a base
  change of a morphism of fppf sheaves is Zariski local on the test object.
* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_and_isEtaleULift_pullback_of_stageSquare`:
  at one test object through which the point factors, the base change is an algebraic space and
  its projection is étale.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_compact_stageSquares`: the
  factorization-free form of `isRepresentableEtale_of_stageSquares`, asking the factorization
  only at quasi-compact test objects and the representability clause as a hypothesis.

## Implementation notes

The locality proof runs through the *source* form of Zariski locality,
`AlgebraicGeometry.Space.relative_etaleOnSite_of_openCover_source`, rather than a target form:
unfolding `AlgebraicGeometry.Space.IsEtaleULift` turns the étale clause at a test object `U`
into the assertion that every relatively étale scheme-valued point `φ` of the base change has
`φ ≫ pullback.fst` relatively étale, and that composite is the universe-lifted Yoneda image of
a morphism `V ⟶ U` of the site. The affine opens of `U` are pulled back to an open covering of
`V` by `AlgebraicGeometry.exists_restrict_bigFppfOver`, each piece maps to the corresponding
affine open by `AlgebraicGeometry.BigFppfOver.existsUnique_lift_of_isOpenImmersion`, and the
restriction of `φ` to a piece lifts to the base change over that affine open because the
comparison morphism between the two base changes is a monomorphism — the affine open being an
open immersion — so `CategoryTheory.MorphismProperty.relative_of_comp_mono` applies. No
coproduct of the pieces is formed, which is what keeps the argument free of cardinal
arithmetic.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison morphism of base changes along a morphism of the site. -/
private noncomputable def cmp {X Z : FppfSheaf B S hS} (ζ : X ⟶ Z) {U U' : BigFppfOver B S hS}
    (c : U' ⟶ U) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj) :
    pullback ((uliftYoneda.{u + 1}).map c ≫ ξ) ζ.hom ⟶ pullback ξ ζ.hom :=
  pullback.lift (pullback.fst _ _ ≫ (uliftYoneda.{u + 1}).map c) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

private theorem cmp_fst {X Z : FppfSheaf B S hS} (ζ : X ⟶ Z) {U U' : BigFppfOver B S hS}
    (c : U' ⟶ U) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj) :
    cmp B S hS ζ c ξ ≫ pullback.fst ξ ζ.hom
      = pullback.fst ((uliftYoneda.{u + 1}).map c ≫ ξ) ζ.hom ≫ (uliftYoneda.{u + 1}).map c :=
  pullback.lift_fst _ _ _

private theorem cmp_snd {X Z : FppfSheaf B S hS} (ζ : X ⟶ Z) {U U' : BigFppfOver B S hS}
    (c : U' ⟶ U) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj) :
    cmp B S hS ζ c ξ ≫ pullback.snd ξ ζ.hom
      = pullback.snd ((uliftYoneda.{u + 1}).map c ≫ ξ) ζ.hom :=
  pullback.lift_snd _ _ _

/-- The comparison is a monomorphism when the morphism of the site is. -/
private theorem mono_cmp {X Z : FppfSheaf B S hS} (ζ : X ⟶ Z) {U U' : BigFppfOver B S hS}
    (c : U' ⟶ U) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj)
    (hc : Mono ((uliftYoneda.{u + 1}).map c)) :
    Mono (cmp B S hS ζ c ξ) := by
  refine ⟨fun {W} α β hαβ ↦ ?_⟩
  refine pullback.hom_ext ?_ ?_
  · refine (cancel_mono ((uliftYoneda.{u + 1}).map c)).1 ?_
    have h := congrArg (fun t ↦ t ≫ pullback.fst ξ ζ.hom) hαβ
    simp only [Category.assoc, cmp_fst] at h
    simpa only [Category.assoc] using h
  · have h := congrArg (fun t ↦ t ≫ pullback.snd ξ ζ.hom) hαβ
    simp only [Category.assoc, cmp_snd] at h
    simpa using h


/-- **Étaleness of a base change of a morphism of fppf sheaves is Zariski local on the test
object.** -/
theorem isEtaleULift_pullback_fst_of_affine
    {X Z : FppfSheaf B S hS} (ζ : X ⟶ Z)
    (haff : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ θ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj,
        Space.IsEtaleULift.{u + 1} B S hS (pullback.fst θ ζ.hom))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj) :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ ζ.hom) := by
  classical
  intro V φ hφ
  obtain ⟨I, Ua, ga, hUaaff, hgaoi, hcovU, -, -⟩ := exists_affineOpens_cover_site' B S hS U
  set gV : V ⟶ U := (uliftYoneda.{u + 1}).preimage (φ ≫ pullback.fst ξ ζ.hom) with hgVdef
  have hgV : (uliftYoneda.{u + 1}).map gV = φ ≫ pullback.fst ξ ζ.hom :=
    (uliftYoneda.{u + 1}).map_preimage _
  -- the preimages in `V` of the affine opens of `U`
  choose Va ka hkaoi hkarange _ using fun a : I ↦ exists_restrict_bigFppfOver V
    ((BigFppfOver.toScheme B S hS).map gV ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map (ga a)).opensRange)
  have hsub : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (ka a ≫ gV)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (ga a)) := by
    intro a y hy
    obtain ⟨x, rfl⟩ := hy
    have hx : (BigFppfOver.toScheme B S hS).map (ka a) x ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (ka a)) := ⟨x, rfl⟩
    rw [hkarange a] at hx
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hx
  choose la hla _ using fun a : I ↦ BigFppfOver.existsUnique_lift_of_isOpenImmersion
    (ga a) (hgaoi a) (ka a ≫ gV) (hsub a)
  -- `{V a ⟶ V}` is an open covering of `V`
  have hcovV : ∀ x : (BigFppfOver.toScheme B S hS).obj V,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ka a)) := by
    intro x
    obtain ⟨a, ha⟩ := hcovU ((BigFppfOver.toScheme B S hS).map gV x)
    refine ⟨a, ?_⟩
    rw [hkarange a]
    exact ha
  -- it suffices to see that each `V a ⟶ U` is étale
  refine Space.relative_etaleOnSite_of_openCover_source B S hS
    (hgV ▸ Functor.relativelyRepresentable.map (uliftYoneda.{u + 1}) gV) ka hkaoi hcovV
    fun a ↦ ?_
  have := hgaoi a
  have := hkaoi a
  -- the restriction of `φ` to the `a`-th piece, read over the affine open `U a`
  have hcond : (uliftYoneda.{u + 1}).map (la a) ≫
      ((uliftYoneda.{u + 1}).map (ga a) ≫ ξ)
      = ((uliftYoneda.{u + 1}).map (ka a) ≫ φ ≫ pullback.snd ξ ζ.hom) ≫ ζ.hom := by
    have h1 : (uliftYoneda.{u + 1}).map (la a) ≫ (uliftYoneda.{u + 1}).map (ga a)
        = (uliftYoneda.{u + 1}).map (ka a) ≫ (uliftYoneda.{u + 1}).map gV := by
      rw [← Functor.map_comp, ← Functor.map_comp, hla a]
    calc (uliftYoneda.{u + 1}).map (la a) ≫ (uliftYoneda.{u + 1}).map (ga a) ≫ ξ
        = ((uliftYoneda.{u + 1}).map (la a) ≫ (uliftYoneda.{u + 1}).map (ga a)) ≫ ξ := by
          rw [Category.assoc]
      _ = ((uliftYoneda.{u + 1}).map (ka a) ≫ (uliftYoneda.{u + 1}).map gV) ≫ ξ := by rw [h1]
      _ = (uliftYoneda.{u + 1}).map (ka a) ≫ (φ ≫ pullback.fst ξ ζ.hom) ≫ ξ := by
          rw [Category.assoc, hgV]
      _ = ((uliftYoneda.{u + 1}).map (ka a) ≫ φ ≫ pullback.snd ξ ζ.hom) ≫ ζ.hom := by
          rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition]
  set χ : (uliftYoneda.{u + 1}).obj (Va a) ⟶
      pullback ((uliftYoneda.{u + 1}).map (ga a) ≫ ξ) ζ.hom :=
    pullback.lift _ _ hcond with hχdef
  have hχfst : χ ≫ pullback.fst ((uliftYoneda.{u + 1}).map (ga a) ≫ ξ) ζ.hom
      = (uliftYoneda.{u + 1}).map (la a) := pullback.lift_fst _ _ _
  have hχsnd : χ ≫ pullback.snd ((uliftYoneda.{u + 1}).map (ga a) ≫ ξ) ζ.hom
      = (uliftYoneda.{u + 1}).map (ka a) ≫ φ ≫ pullback.snd ξ ζ.hom :=
    pullback.lift_snd _ _ _
  -- `χ` composed with the comparison is the restriction of `φ`, which is relatively étale
  have hmonoga : Mono ((uliftYoneda.{u + 1}).map (ga a)) :=
    mono_uliftYoneda_map B S hS (ga a)
      ((BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance)
  have hcmp : χ ≫ cmp B S hS ζ (ga a) ξ = (uliftYoneda.{u + 1}).map (ka a) ≫ φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, cmp_fst, ← Category.assoc, hχfst, ← Functor.map_comp, hla a,
        Functor.map_comp, Category.assoc, hgV]
    · rw [Category.assoc, cmp_snd, hχsnd, Category.assoc]
  have hrestr : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
      ((uliftYoneda.{u + 1}).map (ka a) ≫ φ) :=
    Space.relative_comp B S hS
      ((Space.relative_etale_uliftYoneda_map_iff B S hS (ka a)).mpr inferInstance) hφ
  have hχet : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) χ := by
    have _ : Mono (cmp B S hS ζ (ga a) ξ) := mono_cmp B S hS ζ (ga a) ξ hmonoga
    exact MorphismProperty.relative_of_comp_mono (uliftYoneda.{u + 1}) _ _
      (cmp B S hS ζ (ga a) ξ) (hcmp ▸ hrestr)
  -- the affine case gives that `V a ⟶ U a` is étale
  have hlaet : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
      ((uliftYoneda.{u + 1}).map (la a)) := by
    have h := haff (Ua a) (hUaaff a) ((uliftYoneda.{u + 1}).map (ga a) ≫ ξ) (Va a) χ hχet
    rwa [hχfst] at h
  have hlaetale : Etale ((BigFppfOver.toScheme B S hS).map (la a)) :=
    (Space.relative_etale_uliftYoneda_map_iff B S hS (la a)).mp hlaet
  have hcomp : Etale ((BigFppfOver.toScheme B S hS).map (ka a ≫ gV)) := by
    rw [hla a |>.symm, Functor.map_comp]
    exact inferInstance
  rw [← hgV, ← Functor.map_comp]
  exact (Space.relative_etale_uliftYoneda_map_iff B S hS (ka a ≫ gV)).mpr hcomp

/-! ### The base change at one test object through which the point factors -/

/-- **At a test object through which the point factors, the base change of `ζ` is an algebraic
space and its projection is étale.** This is the pointwise content of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`, isolated so that it can
be used at the affine opens of a point rather than at the point itself. -/
theorem isAlgebraicSpaceULift_and_isEtaleULift_pullback_of_stageSquare {Λ : Type*}
    {X Z : FppfSheaf B S hS} {Y W : Λ → FppfSheaf B S hS} (ζ : X ⟶ Z)
    (p : ∀ i, Y i ⟶ X) (a : ∀ i, Y i ⟶ W i) (ψ : ∀ i, W i ⟶ Z)
    (ha : ∀ i, IsRepresentableEtale B S hS (a i))
    (hsq : ∀ i, IsPullback (p i) (a i) ζ (ψ i))
    {T : BigFppfOver B S hS} (θ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj)
    (hfac : ∃ (i : Λ) (θ' : (uliftYoneda.{u + 1}).obj T ⟶ (W i).obj),
      θ = θ' ≫ (ψ i).hom) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback θ ζ.hom) ∧
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst θ ζ.hom) := by
  classical
  obtain ⟨i, θ', hθ⟩ := hfac
  have hsqP : IsPullback (p i).hom (a i).hom ζ.hom (ψ i).hom :=
    (hsq i).map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hcomp : IsPullback (pullback.fst θ' (a i).hom)
      (pullback.snd θ' (a i).hom ≫ (p i).hom) (θ' ≫ (ψ i).hom) ζ.hom :=
    (IsPullback.of_hasPullback θ' (a i).hom).paste_vert hsqP.flip
  rw [← hθ] at hcomp
  refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS hcomp.isoPullback ((ha i).1 T θ'), ?_⟩
  have h1 : Space.IsEtaleULift.{u + 1} B S hS
      (hcomp.isoPullback.hom ≫ pullback.fst θ ζ.hom) := by
    rw [hcomp.isoPullback_hom_fst]
    exact (ha i).2 T θ'
  have h2 := isEtaleULift_precomp_iso B S hS hcomp.isoPullback.symm
    (hcomp.isoPullback.hom ≫ pullback.fst θ ζ.hom) h1
  simpa using h2

/-! ### The factorization at a quasi-compact test object -/

attribute [local instance] Sheaf.instHasColimitsOfSize

/-! ### Representable étaleness from the quasi-compact factorization -/

/-- **The factorization-free form of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_stageSquares`.** A morphism of fppf
sheaves whose base changes along a family `ψ` are representable étale, cartesianly, is
representable étale as soon as every scheme-valued point of its target *out of a quasi-compact
object of the site* factors through a member of the family — granted the representability
clause.

The étale clause needs only the quasi-compact factorization: it is Zariski local on the test
object by `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_of_affine`, and an affine
object of the site is quasi-compact. The representability clause is the hypothesis `hrep`; it
is what the "modulo set-theoretic issues" of Stacks 0AIS covers here, the atlases of the base
changes over the affine opens of a point needing a uniform size bound below the site's cutoff
to be assembled into one object of the site, which étaleness does not supply. -/
theorem isRepresentableEtale_of_compact_stageSquares {Λ : Type*}
    {X Z : FppfSheaf B S hS} {Y W : Λ → FppfSheaf B S hS} (ζ : X ⟶ Z)
    (p : ∀ i, Y i ⟶ X) (a : ∀ i, Y i ⟶ W i) (ψ : ∀ i, W i ⟶ Z)
    (ha : ∀ i, IsRepresentableEtale B S hS (a i))
    (hsq : ∀ i, IsPullback (p i) (a i) ζ (ψ i))
    (hfac : ∀ (T : BigFppfOver B S hS),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ θ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj,
        ∃ (i : Λ) (θ' : (uliftYoneda.{u + 1}).obj T ⟶ (W i).obj), θ = θ' ≫ (ψ i).hom)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ζ.hom) :
    IsRepresentableEtale B S hS ζ := by
  refine ⟨hrep, fun U ξ ↦ ?_⟩
  refine isEtaleULift_pullback_fst_of_affine B S hS ζ (fun T hT θ ↦ ?_) U ξ
  have hTcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := by
    have := hT; infer_instance
  exact (isAlgebraicSpaceULift_and_isEtaleULift_pullback_of_stageSquare B S hS ζ p a ψ ha hsq
    θ (hfac T hTcompact θ)).2

end AlgebraicGeometry.FormalSpace

end
