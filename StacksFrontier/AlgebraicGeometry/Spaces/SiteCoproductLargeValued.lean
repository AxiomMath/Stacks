module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coproduct of a uniformly bounded family of the big fppf site, among sheaves of `Type (u+1)`

A big fppf site `B` contains the coproduct of a family of its schemes as soon as the index type
and the components carry one common size bound below the cutoff, and the representable sheaf of
that coproduct — formed among sheaves of `Type (u + 1)`, the value universe in which a formal
algebraic space over `S` lives — is the coproduct of the representable sheaves of the members.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_sigma_of_size_le`: a big fppf site contains the
  coproduct of a family of its schemes of uniformly bounded size, indexed by a type of
  cardinality below the same bound.
* `AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaCofan`: if the underlying scheme of an
  object `V` of the big fppf site of `S` is the coproduct of the underlying schemes of a family
  `X`, then the universe-lifted representable sheaf of `V` is the coproduct, among fppf sheaves
  of `Type (u + 1)`, of the universe-lifted representable sheaves of the `X i`.
* `AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`: the two put together.
  A uniformly bounded family of objects of the big fppf site of `S` has a coproduct `V` in that
  site, computed on underlying schemes, whose injections are open immersions covering `V`, and
  the universe-lifted representable sheaf of `V` is the coproduct of those of the members.
* `AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_etaleCover`: a uniformly
  bounded family of morphisms into an object of the site, étale on underlying schemes and
  covering it, is refined by a single surjective étale morphism out of one object of the site,
  namely the coproduct of the family.
* `AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_openCover`: the same for a
  uniformly bounded open covering.
* `AlgebraicGeometry.BigFppfOver.exists_affineOpens_surjective_etale_sigma`: every object of
  the site — quasi-compact or not — is covered surjectively and étale by one object of the
  site which is the coproduct of its affine opens.

## Implementation notes

*Why the size bound and not a cofinality bound.*
`AlgebraicGeometry.BigFppfSite.contains_sigma` already puts the coproduct of a family of schemes
of the site in the site, but under `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which
asks for `#ι` below the *cofinality* of the cutoff. That hypothesis is the right one for a
family whose members are known only to lie in the site, since a cutoff produced by Tag 000J need
not be regular and a supremum of `#ι` many cardinals below it can reach it. It is the wrong one
for the family this file is built for — the affine opens of a single object `T` of the site —
because `#T.affineOpens` carries no cofinality bound. That family does carry a *uniform* bound:
both the index type and every member have size at most `T.size`, which is below the cutoff, and
`AlgebraicGeometry.schemeSize_coproduct_le` bounds the coproduct by it directly.

*Why the value universe `Type (u + 1)`.*
`AlgebraicGeometry.BigFppfOver.isColimit_yoneda_cofan` is the same statement for sheaves of
`Type u`, the value universe of the site. A formal algebraic space over `S` is a sheaf of
`Type (u + 1)`, so a coproduct of representables occurring in that theory is formed among
sheaves of `Type (u + 1)` and the statement in the value universe of the site does not apply to
it. The descent criterion behind both is the same;
`CategoryTheory.GrothendieckTopology.isColimitCofanMkUliftYoneda` is its universe-raising form.

*What makes the criterion apply.* The injections into a coproduct of schemes are open
immersions, jointly surjective, pairwise disjoint and monomorphisms, and each of those four
facts transports to `V` along the comparison isomorphism `∐ᵢ Xᵢ ≅ V` supplied by the hypothesis.
Joint surjectivity by open immersions makes the injections generate a covering sieve of the fppf
topology (`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`), and
disjointness makes the pairwise intersections initial, which is
`AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne` read in the slice.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe v u

namespace AlgebraicGeometry

/-- The topology of the big fppf site over `S` is subcanonical, being the slice of the
subcanonical topology of the big fppf site. -/
@[sga "3 IV 4.5.3" "special case"]
instance bigFppfOver_topology_subcanonical (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (BigFppfOver.topology B S hS).Subcanonical := by
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  change (B.topology.over (B.obj hS)).Subcanonical
  infer_instance

/-- A big fppf site contains the coproduct of a family of schemes it contains carrying a
uniform size bound below the cutoff, the index type being of cardinality at most that bound.

Unlike `AlgebraicGeometry.BigFppfSite.contains_sigma` this asks nothing of the cofinality of the
cutoff: the uniform bound already dominates the supremum of the component sizes, so
`AlgebraicGeometry.schemeSize_coproduct_le` applies to the bound itself, enlarged to be
infinite. -/
theorem BigFppfSite.contains_sigma_of_size_le (B : BigFppfSite.{u}) {ι : Type u}
    (Y : ι → Scheme.{u}) {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hY : ∀ i, (Y i).size ≤ μ) : B.Contains (∐ Y) :=
  (schemeSize_coproduct_le Y (max μ ℵ₀) (le_max_right _ _) (hι.trans (le_max_left _ _))
    fun i => (hY i).trans (le_max_left _ _)).trans_lt (max_lt hμ B.aleph0_lt_cutoff)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cofan

variable {ι : Type v} [Small.{u} ι] (X : ι → BigFppfOver B S hS)
  {V : BigFppfOver B S hS} (j : ∀ i, X i ⟶ V)
  (hj : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
    fun i => (toScheme B S hS).map (j i)))

include hj

/-- The injections of a cofan of the big fppf site of `S` whose underlying scheme cofan is a
coproduct are open immersions: each is the corresponding coproduct injection of schemes
followed by the comparison isomorphism. -/
theorem isOpenImmersion_toScheme_map_of_isColimit (i : ι) :
    IsOpenImmersion ((toScheme B S hS).map (j i)) := by
  set Y : ι → Scheme.{u} := fun k => (toScheme B S hS).obj (X k)
  have hfac : Sigma.ι Y i ≫ ((coproductIsCoproduct Y).coconePointUniqueUpToIso hj).hom =
      (toScheme B S hS).map (j i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hj (Discrete.mk i)
  rw [← hfac]
  infer_instance

/-- The injections of a cofan of the big fppf site of `S` whose underlying scheme cofan is a
coproduct cover the underlying scheme of its vertex. -/
theorem exists_mem_range_toScheme_map_of_isColimit (x : (toScheme B S hS).obj V) :
    ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i)) := by
  set Y : ι → Scheme.{u} := fun k => (toScheme B S hS).obj (X k)
  set e : (∐ Y) ≅ (toScheme B S hS).obj V :=
    (coproductIsCoproduct Y).coconePointUniqueUpToIso hj
  have hfac : ∀ i, Sigma.ι Y i ≫ e.hom = (toScheme B S hS).map (j i) := fun i =>
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hj (Discrete.mk i)
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq (e.inv.base x)
  have hy' : (Sigma.ι Y (i : ι)) y = e.inv x := hy
  refine ⟨i, y, ?_⟩
  calc ((toScheme B S hS).map (j (i : ι))) y
      = (Sigma.ι Y (i : ι) ≫ e.hom) y := by rw [hfac i]
    _ = e.hom ((Sigma.ι Y (i : ι)) y) := rfl
    _ = e.hom (e.inv x) := by rw [hy']
    _ = x := by simp

/-- **The coproduct of universe-lifted representables.** If the underlying scheme of an object
`V` of the big fppf site of `S` is the coproduct of the underlying schemes of a family `X`, with
the injections of the family as coproduct injections, then the universe-lifted representable
sheaf of `V` is the coproduct, among fppf sheaves of `Type (u + 1)`, of the universe-lifted
representable sheaves of the `X i`.

No size hypothesis appears: the containment of the coproduct in the site is already carried by
the existence of `V`. -/
def isColimitUliftYonedaCofan :
    IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
      fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i)) := by
  set Y : ι → Scheme.{u} := fun k => (toScheme B S hS).obj (X k) with hYdef
  set e : (∐ Y) ≅ (toScheme B S hS).obj V :=
    (coproductIsCoproduct Y).coconePointUniqueUpToIso hj with hedef
  have hfac : ∀ i, Sigma.ι Y i ≫ e.hom = (toScheme B S hS).map (j i) := fun i =>
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hj (Discrete.mk i)
  have hmono : ∀ i, Mono (j i) := by
    intro i
    apply (Over.forget (B.obj hS)).mono_of_mono_map
    apply B.inclusion.mono_of_mono_map
    change Mono ((toScheme B S hS).map (j i))
    rw [← hfac i]
    infer_instance
  let _ : ∀ i, Mono ((Cofan.mk V j).inj i) := hmono
  refine (BigFppfOver.topology B S hS).isColimitCofanMkUliftYoneda (c := Cofan.mk V j) X
    (ofArrows_mem_topology_of_isOpenImmersion B S hS j
      (isOpenImmersion_toScheme_map_of_isColimit B S hS X j hj)
      (exists_mem_range_toScheme_map_of_isColimit B S hS X j hj))
    (bot_mem_topology_of_isInitial B S hS) ?_
  intro i i' hii' Z a b hab
  have hab' : (toScheme B S hS).map a ≫ Sigma.ι Y i =
      (toScheme B S hS).map b ≫ Sigma.ι Y i' := by
    have h : (toScheme B S hS).map a ≫ (toScheme B S hS).map (j i) =
        (toScheme B S hS).map b ≫ (toScheme B S hS).map (j i') := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (toScheme B S hS).map hab
    rw [← hfac i, ← hfac i', ← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono e.hom).mp h
  have hZ : IsEmpty ((toScheme B S hS).obj Z) := isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ hii'
  exact ⟨Over.isInitialOfIsInitialLeft (Y := Z)
    (isInitial_schemeBelow B (isInitial_iff_isEmpty.mpr hZ).some)⟩

/-- A cofan of the big fppf site of `S` whose underlying scheme cofan is a coproduct is a
coproduct: the inclusion of the site into schemes is the composite of a slice forgetful functor,
which creates colimits, with a fully faithful functor, which reflects them. -/
def isColimitCofanOfIsColimitToScheme : IsColimit (Cofan.mk V j) := by
  have hleft : IsColimit (Cofan.mk V.left fun i => (j i).left) := by
    apply isColimitOfReflects B.inclusion
    exact (Cofan.isColimitMapCoconeEquiv B.inclusion (fun i => (X i).left)
      (Cofan.mk V.left fun i => (j i).left)).2 hj
  exact isColimitOfReflects (Over.forget (B.obj hS))
    ((Cofan.isColimitMapCoconeEquiv (Over.forget (B.obj hS)) X (Cofan.mk V j)).symm hleft)

end Cofan

/-- **The coproduct of a uniformly bounded family of the big fppf site of `S`, and its
representable sheaf of `Type (u + 1)`.**

A family `X` of objects of the big fppf site of `S` whose index type and whose underlying
schemes all have size at most one cardinal `μ` below the site's cutoff has a coproduct `V` in
the site; the coproduct is computed on underlying schemes, its injections are open immersions
covering `V`, and the universe-lifted representable sheaf of `V` is the coproduct, among fppf
sheaves of `Type (u + 1)`, of the universe-lifted representable sheaves of the `X i`.

The bound is the one an affine open covering of an object `T` of the site supplies: there are at
most `T.size` affine opens of `T` (`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`) and each
has size at most `T.size` (`AlgebraicGeometry.Scheme.size_coe_opens_le`), so `μ := T.size` serves
and is below the cutoff because `T` is in the site. No cofinality bound is needed. -/
theorem exists_isColimitUliftYoneda_of_size_le {ι : Type u} (X : ι → BigFppfOver B S hS)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V),
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      (∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i))) ∧
      Nonempty (IsColimit (Cofan.mk ((toScheme B S hS).obj V)
        fun i => (toScheme B S hS).map (j i))) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) := by
  set Y : ι → Scheme.{u} := fun i => (toScheme B S hS).obj (X i)
  have hcon : B.Contains (∐ Y) := B.contains_sigma_of_size_le Y hμ hι hX
  let V : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage (X := B.obj hcon) (Y := B.obj hS)
      (Sigma.desc fun i => B.inclusion.map (X i).hom))
  let j : ∀ i, X i ⟶ V := fun i =>
    Over.homMk (B.inclusion.preimage (X := (X i).left) (Y := B.obj hcon) (Sigma.ι Y i)) (by
      apply B.inclusion.map_injective
      show B.inclusion.map (B.inclusion.preimage (X := (X i).left) (Y := B.obj hcon)
          (Sigma.ι Y i) ≫ B.inclusion.preimage (X := B.obj hcon) (Y := B.obj hS)
          (Sigma.desc fun k => B.inclusion.map (X k).hom)) = _
      rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
      exact Sigma.ι_desc _ i)
  have hmap : ∀ i, (toScheme B S hS).map (j i) = Sigma.ι Y i := fun i =>
    B.inclusion.map_preimage _
  have hj : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
      fun i => (toScheme B S hS).map (j i)) := by
    refine IsColimit.ofIsoColimit (coproductIsCoproduct Y) (Cofan.ext (Iso.refl _) fun i => ?_)
    simp only [Iso.refl_hom, Category.comp_id]
    exact (hmap i).symm
  exact ⟨V, j, isOpenImmersion_toScheme_map_of_isColimit B S hS X j hj,
    exists_mem_range_toScheme_map_of_isColimit B S hS X j hj, ⟨hj⟩,
    ⟨isColimitCofanOfIsColimitToScheme B S hS X j hj⟩,
    ⟨isColimitUliftYonedaCofan B S hS X j hj⟩⟩

/-- **A uniformly bounded étale covering of an object of the site is refined by a single
surjective étale morphism out of one object of the site.**

Given a family `g : X i ⟶ T` of morphisms étale on underlying schemes whose images cover `T`
and whose index type and members are bounded by one cardinal below the cutoff, the coproduct
`V` of the `X i` lies in the site and the induced `q : V ⟶ T` is surjective and étale; the
universe-lifted representable sheaf of `V` is the coproduct, among fppf sheaves of
`Type (u + 1)`, of those of the `X i`.

This is the shape in which a *non-quasi-compact* object of the site supplies a covering by one
object of the site: the covering family may be infinite, so no finite coproduct suffices, and
only a uniform size bound — not a cofinality bound — is available for it. The members of the
family need not be open immersions; the injections of the coproduct are, which is what makes
étaleness of `q` local on its source. -/
theorem exists_surjective_etale_sigma_of_etaleCover {ι : Type u} (X : ι → BigFppfOver B S hS)
    (T : BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hg : ∀ i, Etale ((toScheme B S hS).map (g i)))
    (hcov : ∀ x : (toScheme B S hS).obj T, ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V) (q : V ⟶ T),
      (∀ i, j i ≫ q = g i) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      (∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i))) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Etale ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) := by
  obtain ⟨V, j, hjopen, hjcov, -, ⟨hjsite⟩, hjsheaf⟩ :=
    exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  have hfac (i : ι) : (toScheme B S hS).map (j i) ≫
      (toScheme B S hS).map (Cofan.IsColimit.desc hjsite g) = (toScheme B S hS).map (g i) := by
    rw [← Functor.map_comp]
    exact congrArg (toScheme B S hS).map (Cofan.IsColimit.fac hjsite g i)
  refine ⟨V, j, Cofan.IsColimit.desc hjsite g, fun i => Cofan.IsColimit.fac hjsite g i,
    hjopen, hjcov, ?_, ?_, ⟨hjsite⟩, hjsheaf⟩
  · rw [surjective_iff]
    intro t
    obtain ⟨i, y, hy⟩ := hcov t
    refine ⟨((toScheme B S hS).map (j i)) y, ?_⟩
    calc ((toScheme B S hS).map (Cofan.IsColimit.desc hjsite g)) (((toScheme B S hS).map (j i)) y)
        = ((toScheme B S hS).map (j i) ≫
            (toScheme B S hS).map (Cofan.IsColimit.desc hjsite g)) y := rfl
      _ = ((toScheme B S hS).map (g i)) y := by rw [hfac i]
      _ = t := hy
  · let 𝒰 : ((toScheme B S hS).obj V).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (toScheme B S hS).obj (X i)
        f := fun i => (toScheme B S hS).map (j i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjcov, hjopen⟩ }
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    show Etale ((toScheme B S hS).map (j i) ≫ _)
    rw [hfac i]
    exact hg i

/-- **A uniformly bounded open covering of an object of the site is refined by a single
surjective étale morphism out of one object of the site.** This is
`AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_etaleCover` for a family of
open immersions, which are in particular étale. -/
theorem exists_surjective_etale_sigma_of_openCover {ι : Type u} (X : ι → BigFppfOver B S hS)
    (T : BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hg : ∀ i, IsOpenImmersion ((toScheme B S hS).map (g i)))
    (hcov : ∀ x : (toScheme B S hS).obj T, ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V) (q : V ⟶ T),
      (∀ i, j i ≫ q = g i) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Etale ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) := by
  obtain ⟨V, j, q, hjq, -, -, hqsurj, hqet, hsite, hsheaf⟩ :=
    exists_surjective_etale_sigma_of_etaleCover B S hS X T g
      (fun i => have _ := hg i; inferInstance) hcov hμ hι hX
  exact ⟨V, j, q, hjq, hqsurj, hqet, hsite, hsheaf⟩

/-- **Every object of the big fppf site of `S` is covered, surjectively and étale, by a single
object of the site which is a coproduct of affine opens, and whose universe-lifted representable
sheaf of `Type (u + 1)` is the coproduct of theirs.**

The covering family is the family of *all* affine opens of `T`, which is infinite as soon as `T`
is not quasi-compact; the size bound it satisfies is `μ := T.size`, by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size` on the index and
`AlgebraicGeometry.Scheme.size_coe_opens_le` on the members, and `T.size < B.cutoff` because `T`
lies in the site. No cofinality bound on the number of affine opens is needed, which is what
makes the statement available for an arbitrary `T`. -/
theorem exists_affineOpens_surjective_etale_sigma (T : BigFppfOver B S hS) :
    ∃ (ι : Type u) (X : ι → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V)
      (q : V ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (X i))) ∧
      #ι ≤ ((toScheme B S hS).obj T).size ∧
      (∀ i, ((toScheme B S hS).obj (X i)).size ≤ ((toScheme B S hS).obj T).size) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Etale ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) := by
  set W : Scheme.{u} := (toScheme B S hS).obj T
  let hU (i : W.affineOpens) : B.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let f (i : W.affineOpens) : B.obj (hU i) ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hU i)) ⟶ B.inclusion.obj T.left from i.1.ι)
  let X (i : W.affineOpens) : BigFppfOver B S hS := Over.mk (f i ≫ T.hom)
  let g (i : W.affineOpens) : X i ⟶ T := Over.homMk (f i) (by simp [X])
  have hfmap (i : W.affineOpens) : (toScheme B S hS).map (g i) = i.1.ι :=
    B.inclusion.map_preimage _
  have hgopen (i : W.affineOpens) : IsOpenImmersion ((toScheme B S hS).map (g i)) := by
    rw [hfmap i]
    infer_instance
  have hgcov : ∀ x : (toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)) := by
    intro x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    rw [hfmap i]
    rfl
  obtain ⟨V, j, q, -, hqsurj, hqetale, hsite, hsheaf⟩ :=
    exists_surjective_etale_sigma_of_openCover B S hS X T g hgopen hgcov T.left.property
      (Scheme.mk_affineOpens_le_size W) fun i => Scheme.size_coe_opens_le W i.1
  exact ⟨W.affineOpens, X, V, j, q, fun i => i.2, Scheme.mk_affineOpens_le_size W,
    fun i => Scheme.size_coe_opens_le W i.1, hqsurj, hqetale, hsite, hsheaf⟩

end BigFppfOver

end AlgebraicGeometry

end
