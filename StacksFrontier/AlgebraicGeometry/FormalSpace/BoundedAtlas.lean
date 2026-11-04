module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveCoproduct

/-!
# An atlas of a formal algebraic space indexed below the cutoff

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. Definition **Stacks 0AIM** gives `X` an atlas `{Xᵢ ⟶ X}` indexed by an arbitrary type
of `Type (u + 1)`, with no bound at all on the index. Every criterion in this library which
assembles a family of charts into a single one — `AlgebraicGeometry.isAlgebraicSpace_coproduct`
and its size-bounded form, `AlgebraicGeometry.FormalSpace.exists_chart_of_size_le` — consumes
instead a family indexed by a type of `Type u` whose cardinality is below the cutoff of the
site, so an unbounded atlas cannot be fed to any of them.

This file removes that obstruction: *every* formal algebraic space already has an atlas indexed
below the cutoff. One keeps the members of the given atlas met by the chosen points of an
object of the site surjecting onto `X`, and throws the rest away.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isFormalAtlas_of_mk_lt_cutoff`: a formal algebraic
  space admits an atlas in the sense of Definition 0AIM indexed by (the universe lift of) a
  type of `Type u` of cardinality below the cutoff of the site.
* `AlgebraicGeometry.FormalSpace.exists_isFormalAtlas_pullback_cover_of_mk_lt_cutoff`: that
  atlas, base changed along an arbitrary morphism of fppf sheaves into the formal algebraic
  space, is still jointly surjective. This is the shape in which the proof of **Stacks 0AIP**
  consumes an atlas.

## Implementation notes

The set-theoretic condition of **Stacks 0AIS**, which Definition 0AIM carries, supplies an
object `U` of the site and a surjection of sheaves `h_U ⟶ X`. Pulling the atlas back along it
gives, for each index `i`, an algebraic space `U ×_X Xᵢ` over `S` — the atlas maps are
representable by algebraic spaces, not by objects of the site, which is the one difference
from `AlgebraicGeometry.FormalSpace.isAlgebraicSpace_of_affineSchemeAtlas`, where the members
of the family are affine schemes. Choosing a surjective étale scheme atlas `Zᵢ ⟶ U ×_X Xᵢ` of
each turns the pullback family into a family of étale morphisms `Zᵢ ⟶ U` of objects of the
site which is jointly surjective on points, and one index may be chosen for each point of `U`.
The surviving subfamily is indexed by the points of `U`, and a scheme has at most `2 ^ size`
points while the cutoff is a strong prelimit containing the size of every object of the site.

Joint surjectivity of the subfamily is read off at the level of presheaves: the chosen `Zᵢ ⟶ U`
cover `U` on points and are flat and locally of finite presentation, hence generate a covering
sieve, so the induced map out of the coproduct of the `h_{Zᵢ}` is locally surjective; composing
with `h_U ⟶ X` and factoring through the coproduct of the `Xᵢ` is
`CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_of_fac`. The conclusion is demanded for
the coproduct taken in *sheaves* and over the universe-lifted index type, and the comparison
morphism from the presheaf coproduct over the unlifted one carries it there.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A formal algebraic space has an atlas indexed below the cutoff.** Every formal algebraic
space over `S` admits a family as in Definition **Stacks 0AIM** — affine formal algebraic
spaces, mapping to it representably and étale, jointly surjective — whose index type is the
universe lift of a type of `Type u` of cardinality strictly below the cutoff of the site.

Definition 0AIM puts no bound on the index type of an atlas, while every criterion assembling
charts into one consumes a bounded index. The set-theoretic condition of Stacks 0AIS provides
an object `U` of the site surjecting onto `X`, and keeping one member of the given atlas for
each point of `U` leaves a jointly surjective subfamily; a scheme has at most `2 ^ size` points
and the cutoff is a strong prelimit. -/
theorem exists_isFormalAtlas_of_mk_lt_cutoff (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (K : Type u) (Xi : ULift.{u + 1} K → FppfSheaf B S hS) (f : ∀ k, Xi k ⟶ X),
      Cardinal.mk K < B.cutoff ∧ IsFormalAtlas B S hS X Xi f := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, I, Xi, f, hXi, hf, hcover⟩ := hX
  obtain ⟨U, R, hU, hR, ⟨eU⟩, -, t, ht, -⟩ := hset
  let t' : Y.obj U ⟶ X.obj := eU.inv ≫ t.hom
  have ht' : Presheaf.IsLocallySurjective J t' := by
    have : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    dsimp only [t']
    infer_instance
  have hchart : ∀ i, ∃ (Z : C) (g : Y.obj Z ⟶ pullback t' (f i).hom),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative Y g ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative Y g :=
    fun i => ((hf i).1 U t').exists_atlas
  choose Z g hgs hge using hchart
  let p : ∀ i, Z i ⟶ U := fun i => Y.preimage (g i ≫ pullback.fst t' (f i).hom)
  have hpmap : ∀ i, Y.map (p i) = g i ≫ pullback.fst t' (f i).hom := fun i => Y.map_preimage _
  have hp : ∀ i, Etale (p i).left.hom := by
    intro i
    have h1 := (show Space.IsEtaleULift.{u + 1} B S hS (pullback.fst t' (f i).hom) from
      (hf i).2 U t') (Z i) (g i) (hge i)
    rw [← hpmap i] at h1
    exact MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := Y) h1
  let v : ∀ i, Y.obj (Z i) ⟶ (Xi i).obj := fun i => g i ≫ pullback.snd t' (f i).hom
  have hfac : ∀ i, v i ≫ (f i).hom = Y.map (p i) ≫ t' := fun i => by
    simp only [v, hpmap i, Category.assoc, ← pullback.condition]
  -- every point of `U` is met by some member of the pulled-back family
  have hpoint : ∀ x : U.left.obj, ∃ i, x ∈ Set.range (p i).left.hom := by
    have hmem := family_imageSieve_mem J Xi X f hcover U (uliftYonedaEquiv t')
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨E, hE, hER⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hmem
    have hEF := B.isFppfCovering_of_isCovering hE
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
    intro x
    obtain ⟨j, y, hy⟩ := hEF.1 x
    let T : C := Over.mk (E.f j ≫ U.hom)
    let b : T ⟶ U := Over.homMk (E.f j)
    have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
    change (⨆ i, Presheaf.imageSieve (f i).hom (uliftYonedaEquiv t')) b at hb
    simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
    obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hb
    let m : Y.obj T ⟶ (Xi i).obj := uliftYonedaEquiv.symm z
    have hw : m ≫ (f i).hom = Y.map b ≫ t' := by
      apply uliftYonedaEquiv.injective
      rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} t' b.op)
    let ξ : Y.obj T ⟶ pullback t' (f i).hom := pullback.lift (Y.map b) m hw.symm
    let T' : C := (hgs i).rep.pullback ξ
    let q : T' ⟶ T := (hgs i).rep.snd ξ
    let r : T' ⟶ Z i := Y.preimage ((hgs i).rep.fst ξ)
    have hq : Surjective q.left.hom := (hgs i).property_snd ξ
    have hrp : r ≫ p i = q ≫ b := by
      apply Y.map_injective
      rw [Y.map_comp, Y.map_comp, Y.map_preimage, hpmap i, ← Category.assoc,
        ((hgs i).rep.isPullback ξ).w, Category.assoc]
      simp only [ξ, pullback.lift_fst]
      rfl
    obtain ⟨y', hy'⟩ := hq.1 y
    refine ⟨i, r.left.hom y', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← show (r ≫ p i).left.hom =
      r.left.hom ≫ (p i).left.hom from rfl, hrp,
      show (q ≫ b).left.hom = q.left.hom ≫ b.left.hom from rfl, Scheme.Hom.comp_apply, hy']
    exact hy
  choose idx hidx using hpoint
  -- the surviving subfamily, indexed by the points of `U`
  refine ⟨U.left.obj, fun k => Xi (idx k.down), fun k => f (idx k.down),
    (mk_scheme_le_two_power_size U.left.obj).trans_lt (B.cutoff_isStrongPrelimit U.left.property),
    fun k => hXi (idx k.down), fun k => hf (idx k.down), ?_⟩
  -- joint surjectivity
  have hmem : Sieve.ofArrows (fun x : U.left.obj => Z (idx x))
      (fun x => p (idx x)) ∈ J U :=
    fppf_ofArrows_mem B S hS _ _
      (fun x => by have := hp (idx x); infer_instance)
      (fun x => by have := hp (idx x); infer_instance)
      (fun x => ⟨x, hidx x⟩)
  have hu : Presheaf.IsLocallySurjective J
      (Sigma.desc (fun x : U.left.obj => Y.map (p (idx x)))) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
      J (fun x : U.left.obj => p (idx x))).mp hmem
  have hps : Presheaf.IsLocallySurjective J
      (Sigma.desc (fun x : U.left.obj => (f (idx x)).hom)) :=
    Presheaf.isLocallySurjective_sigmaDesc_of_fac J _
      (fun x : U.left.obj => Y.map (p (idx x))) (fun x : U.left.obj => v (idx x)) t'
      hu ht' (fun x => hfac (idx x))
  let c : (∐ fun x : U.left.obj => (Xi (idx x)).obj) ⟶
      (∐ fun k : ULift.{u + 1} U.left.obj => Xi (idx k.down)).obj :=
    Sigma.desc fun x => (Sigma.ι (fun k : ULift.{u + 1} U.left.obj => Xi (idx k.down))
      (ULift.up x)).hom
  have hc : c ≫ (Sigma.desc fun k : ULift.{u + 1} U.left.obj =>
      f (idx k.down)).hom = Sigma.desc (fun x : U.left.obj => (f (idx x)).hom) := by
    refine Sigma.hom_ext _ _ fun x => ?_
    rw [← Category.assoc, Sigma.ι_desc]
    change ((Sigma.ι (fun k : ULift.{u + 1} U.left.obj => Xi (idx k.down)) (ULift.up x)) ≫
      Sigma.desc fun k : ULift.{u + 1} U.left.obj => f (idx k.down)).hom = _
    rw [Sigma.ι_desc, Sigma.ι_desc]
  have : Presheaf.IsLocallySurjective J
      (c ≫ (Sigma.desc fun k : ULift.{u + 1} U.left.obj => f (idx k.down)).hom) := by
    rwa [hc]
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J c _

/-- **The atlas of a formal algebraic space, pulled back along an arbitrary morphism, still
covers and is still indexed below the cutoff.** For `X` a formal algebraic space over `S` and
`φ : P ⟶ X` any morphism of fppf sheaves, the base changes `Xₖ ×_X P ⟶ P` of an atlas as in
Definition **Stacks 0AIM** indexed below the cutoff are again jointly surjective.

This is the form in which the proof of **Stacks 0AIP** consumes an atlas: there `P` is the
relative product of two scheme-valued points of `X`, and the base changes are the members of
the cover of it whose algebraicity is
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_snd_pullback_snd`. -/
theorem exists_isFormalAtlas_pullback_cover_of_mk_lt_cutoff (X P : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X) (φ : P ⟶ X) :
    ∃ (K : Type u) (Xi : ULift.{u + 1} K → FppfSheaf B S hS) (f : ∀ k, Xi k ⟶ X),
      Cardinal.mk K < B.cutoff ∧ IsFormalAtlas B S hS X Xi f ∧
        letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective (Sigma.desc fun k => pullback.snd (f k) φ) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨K, Xi, f, hK, hatlas⟩ := exists_isFormalAtlas_of_mk_lt_cutoff B S hS X hX
  exact ⟨K, Xi, f, hK, hatlas,
    Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ f hatlas.2.2⟩

end AlgebraicGeometry.FormalSpace

end
