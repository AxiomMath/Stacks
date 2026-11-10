module

public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Sites.Preserves
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fpqc sheaf condition for an algebraic space, reduced to single affine morphisms

Let `F` be an algebraic space over `S`. This file shows that `F` preserves finite products, that
the sheaf condition for a finite family of the big fppf category over `S` follows from the sheaf
condition for the single morphism out of its coproduct, and hence that `F` is an fpqc sheaf as
soon as it satisfies the sheaf condition for every surjective flat quasi-compact morphism of the
site between objects with affine underlying scheme.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_iso_sigma_of_isColimit_cofan`: a finite coproduct
  cofan of the big fppf category over `S` becomes a coproduct cofan of schemes.
* `AlgebraicGeometry.BigFppfOver.ofArrows_cofan_inj_mem_fppfPrecoverage`: the injections of a
  finite coproduct cofan form, in schemes, a Zariski and hence fppf covering family.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_empty_of_isInitial`: an algebraic space takes
  the initial object of the site — the empty scheme over `S` — to a singleton.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_ofArrows_cofan_inj`: an algebraic space
  satisfies the sheaf condition for the injections of a finite coproduct cofan.
* `AlgebraicGeometry.IsAlgebraicSpace.preservesLimitsOfShape_discrete`: an algebraic space
  over `S` preserves finite products.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_ofArrows_of_isSheafFor_singleton_cofanDesc`:
  the sheaf condition for a finite family of the site follows from the sheaf condition for the
  single morphism out of its coproduct.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isSheafFor_singleton_affine`: the fpqc
  sheaf condition follows from the sheaf condition for a single surjective flat quasi-compact
  morphism of affine objects.
* `IsAlgebraicSpace.isSheaf_fpqc_of_isIndQuasiAffineHom_of_isEffectiveFpqcDescent`: an
  algebraic space with a surjective étale chart whose underlying scheme is separated is an fpqc
  sheaf, given effective descent along surjective flat quasi-compact morphisms of affine objects
  for the descent data the chart produces.

## Implementation notes

The disjoint union step is Mathlib's `CategoryTheory.Presieve.isSheafFor_sigmaDesc_iff`, which
asks that the coproduct exist, that its cofan be a *universal* colimit, and that the presheaf
preserve the corresponding finite products. The first two hold because the big fppf category
over `S` is finitary extensive, `AlgebraicGeometry.finitaryExtensive_bigFppfOver`.

An algebraic space preserves finite products because it is an fppf sheaf: the injections of a
finite coproduct of the site are, on underlying schemes, open immersions with disjoint images
covering the coproduct, hence a Zariski and so an fppf covering family, and
`CategoryTheory.Presieve.preservesProduct_of_isSheafFor` turns the sheaf condition for that
family into preservation of the product. The nullary case holds because the empty family is an
fppf covering family of the empty scheme. No regularity of `AlgebraicGeometry.BigFppfSite.cutoff`
is needed.

## References

* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 040I](https://stacks.math.columbia.edu/tag/040I)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BigFppfOver

/-! ### Finite coproducts of the site, read in schemes -/

/-- A finite coproduct cofan of the big fppf category over `S` is a coproduct cofan of schemes:
the coproduct of the underlying schemes is isomorphic to the underlying scheme of the cofan
point, compatibly with the injections. -/
theorem exists_iso_sigma_of_isColimit_cofan {ι : Type v} [Finite ι]
    (W : ι → BigFppfOver B S hS) {c : Cofan W} (hc : IsColimit c) :
    ∃ e : (∐ fun i ↦ (toScheme B S hS).obj (W i)) ≅ (toScheme B S hS).obj c.pt,
      ∀ i, Sigma.ι (fun i ↦ (toScheme B S hS).obj (W i)) i ≫ e.hom =
        (toScheme B S hS).map (c.inj i) := by
  have hd : IsColimit (Cofan.mk ((toScheme B S hS).obj c.pt)
      (fun i ↦ (toScheme B S hS).map (c.inj i))) :=
    Cofan.isColimitMapCoconeEquiv (toScheme B S hS) W c (isColimitOfPreserves _ hc)
  refine ⟨(coproductIsCoproduct _).coconePointUniqueUpToIso hd, fun i ↦ ?_⟩
  exact (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hd ⟨i⟩

/-- The injections of a finite coproduct cofan of the big fppf category over `S` are, on
underlying schemes, an fppf covering family. -/
theorem ofArrows_cofan_inj_mem_fppfPrecoverage {ι : Type v} [Finite ι]
    (W : ι → BigFppfOver B S hS) {c : Cofan W} (hc : IsColimit c) :
    Presieve.ofArrows (fun i ↦ (toScheme B S hS).obj (W i))
        (fun i ↦ (toScheme B S hS).map (c.inj i)) ∈
      Scheme.fppfPrecoverage ((toScheme B S hS).obj c.pt) := by
  obtain ⟨e, he⟩ := exists_iso_sigma_of_isColimit_cofan W hc
  have hsurj : ∀ y : (∐ fun i ↦ (toScheme B S hS).obj (W i) : Scheme.{u}),
      ∃ i : ι, y ∈ Set.range (Sigma.ι (fun i ↦ (toScheme B S hS).obj (W i)) i) :=
    fun y ↦ (sigmaOpenCover _).exists_eq y
  refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨i, z, hz⟩ := hsurj (e.inv x)
    refine ⟨i, z, ?_⟩
    rw [← he i, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  · rw [← he i]
    infer_instance

end BigFppfOver

namespace IsAlgebraicSpace

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### An algebraic space preserves finite products -/

/-- An algebraic space satisfies the sheaf condition for a family of the site whose image in
schemes is an fppf covering family. -/
private theorem isSheafFor_ofArrows_of_mem_fppfPrecoverage (hF : IsAlgebraicSpace B S hS F)
    {X : BigFppfOver B S hS} {ι : Type*} (Z : ι → BigFppfOver B S hS) (u : ∀ j, Z j ⟶ X)
    (h : Presieve.ofArrows (fun j ↦ (BigFppfOver.toScheme B S hS).obj (Z j))
        (fun j ↦ (BigFppfOver.toScheme B S hS).map (u j)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj X)) :
    Presieve.IsSheafFor F (Presieve.ofArrows Z u) :=
  (Presieve.isSheafFor_iff_generate _).mpr
    (((isSheaf_iff_isSheaf_of_type _ _).mp hF.isSheaf) _
      (BigFppfOver.sieve_generate_ofArrows_mem_topology Z u h))

/-- An algebraic space satisfies the sheaf condition for the empty family over an initial object
of the site; that is, it takes the initial object to a singleton. -/
theorem isSheafFor_empty_of_isInitial (hF : IsAlgebraicSpace B S hS F)
    {I : BigFppfOver B S hS} (hI : IsInitial I) {ι : Type v} [IsEmpty ι]
    (Z : ι → BigFppfOver B S hS) (u : ∀ j, Z j ⟶ I) :
    Presieve.IsSheafFor F (Presieve.ofArrows Z u) := by
  have hIe : IsEmpty ((BigFppfOver.toScheme B S hS).obj I) :=
    isInitial_iff_isEmpty.mp ⟨hI.isInitialObj (BigFppfOver.toScheme B S hS) I⟩
  refine hF.isSheafFor_ofArrows_of_mem_fppfPrecoverage Z u ?_
  have hbot : Presieve.ofArrows (fun j ↦ (BigFppfOver.toScheme B S hS).obj (Z j))
      (fun j ↦ (BigFppfOver.toScheme B S hS).map (u j)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [Presieve.ofArrows_le_iff]
    intro j
    exact (IsEmpty.false j).elim
  rw [hbot]
  exact Scheme.bot_mem_precoverage _ _

/-- An algebraic space satisfies the sheaf condition for the injections of a finite coproduct
cofan of the site. -/
theorem isSheafFor_ofArrows_cofan_inj (hF : IsAlgebraicSpace B S hS F) {ι : Type v} [Finite ι]
    (W : ι → BigFppfOver B S hS) {c : Cofan W} (hc : IsColimit c) :
    Presieve.IsSheafFor F (Presieve.ofArrows W c.inj) := by
  exact hF.isSheafFor_ofArrows_of_mem_fppfPrecoverage W c.inj
    (BigFppfOver.ofArrows_cofan_inj_mem_fppfPrecoverage W hc)

/-- An algebraic space over `S` preserves finite products. This is the slice analogue of
Mathlib's `AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology`. -/
theorem preservesLimitsOfShape_discrete (hF : IsAlgebraicSpace B S hS F) (ι : Type v)
    [Finite ι] : PreservesLimitsOfShape (Discrete ι) F := by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro Y
  set Z : ι → BigFppfOver B S hS := fun i ↦ unop (Y i) with hZ
  have hmono (i : ι) : Mono ((Cofan.mk (∐ Z) (Sigma.ι Z)).inj i) :=
    inferInstanceAs (Mono (Sigma.ι Z i))
  refine Presieve.preservesProduct_of_isSheafFor F
    (hF.isSheafFor_empty_of_isInitial initialIsInitial _ _) initialIsInitial
    (Cofan.mk (∐ Z) (Sigma.ι Z)) (coproductIsCoproduct Z) (fun i j ↦ ?_)
    (hF.isSheafFor_ofArrows_cofan_inj Z (coproductIsCoproduct Z))
  exact CoproductDisjoint.isPullback_of_isInitial (coproductIsCoproduct Z) initialIsInitial

/-! ### The disjoint union step -/

/-- For an algebraic space over `S`, the sheaf condition for a finite family `{W i ⟶ Y}` of the
big fppf category over `S` follows from the sheaf condition for the single morphism
`⨿ᵢ W i ⟶ Y` out of its coproduct. -/
theorem isSheafFor_ofArrows_of_isSheafFor_singleton_cofanDesc (hF : IsAlgebraicSpace B S hS F)
    {ι : Type v} [Finite ι] {Y : BigFppfOver B S hS} (W : ι → BigFppfOver B S hS)
    (w : ∀ i, W i ⟶ Y) {c : Cofan W} (hc : IsColimit c)
    (h : Presieve.IsSheafFor F (Presieve.singleton (Cofan.IsColimit.desc hc w))) :
    Presieve.IsSheafFor F (Presieve.ofArrows W w) := by
  have h₁ := hF.preservesLimitsOfShape_discrete ι
  have h₂ := hF.preservesLimitsOfShape_discrete (ι × ι)
  exact (Presieve.isSheafFor_sigmaDesc_iff w hc
    (FinitaryExtensive.isVanKampen_finiteCoproducts hc).isUniversal F).mp h

/-- An algebraic space over `S` is a sheaf for the fpqc topology of the big fppf category over
`S` as soon as it satisfies the sheaf condition for the presieve generated by a *single*
morphism of the site whose source and target have affine underlying scheme and whose underlying
morphism of schemes is surjective, flat and quasi-compact. -/
@[sga "3 IV 6.3.1" "(ii), special case"]
theorem isSheaf_fpqc_of_isSheafFor_singleton_affine (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ ⦃Y T : BigFppfOver B S hS⦄ (f : T ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine hF.isSheaf_fpqc_of_isSheafFor_affine_flat_finite fun {Y} m W w hYaff hWaff hwflat
    hmem ↦ ?_
  set G := BigFppfOver.toScheme B S hS
  have hc : IsColimit (Cofan.mk (∐ W) (Sigma.ι W)) := coproductIsCoproduct W
  obtain ⟨e, he⟩ := BigFppfOver.exists_iso_sigma_of_isColimit_cofan W hc
  set g := Cofan.IsColimit.desc hc w
  have hgdesc : G.map g = e.inv ≫ Sigma.desc fun i ↦ G.map (w i) := by
    rw [← Category.id_comp (G.map g), ← e.inv_hom_id, Category.assoc]
    congr 1
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, he i, Sigma.ι_comp_desc, ← Functor.map_comp]
    exact congrArg G.map (Cofan.IsColimit.fac hc w i)
  have hWaff' (i : Fin m) : IsAffine (G.obj (W i)) := hWaff i
  have hTaff : IsAffine (G.obj (Cofan.mk (∐ W) (Sigma.ι W)).pt) :=
    IsAffine.of_isIso e.inv
  have hflat : Flat (G.map g) := by
    have : Flat (Sigma.desc fun i ↦ G.map (w i)) := by
      have hw (i : Fin m) : Flat (G.map (w i)) := hwflat i
      infer_instance
    rw [hgdesc]
    infer_instance
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hmem
  obtain ⟨-, hfl⟩ := hmem
  obtain ⟨hjs, -⟩ := (Scheme.ofArrows_mem_precoverage_iff _).mp hfl
  have hsurj : Surjective (G.map g) := by
    have : Surjective (Sigma.desc fun i ↦ G.map (w i)) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨i, z, hzy⟩ := hjs y
      refine ⟨Sigma.ι (fun i ↦ G.obj (W i)) i z, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      exact hzy
    rw [hgdesc]
    infer_instance
  have hY' : IsAffine (G.obj Y) := hYaff
  exact hF.isSheafFor_ofArrows_of_isSheafFor_singleton_cofanDesc W w hc
    (h g hYaff hTaff hsurj hflat inferInstance)

/-- An algebraic space `F` over `S` is a sheaf for the fpqc topology of the big fppf category
over `S`, given the following two hypotheses.

* A surjective étale chart `u : yoneda.obj U ⟶ F` whose underlying scheme is separated
  (`hUsep`, `hus`, `hue`).
* `hAPK`, effective descent in the form of Stacks 0APK: for every morphism `f : T' ⟶ T` of the
  site between objects with affine underlying scheme whose underlying morphism of schemes is
  surjective, flat and quasi-compact, and every pullback square of `q : V ⟶ U` and
  `p : V ⟶ T'` over `u : yoneda.obj U ⟶ F` and `c : yoneda.obj T' ⟶ F`, where `c` agrees on the
  two projections of `T' ×_T T'` and `p` is surjective, étale, separated and ind-quasi-affine
  on underlying schemes, there are an object `W` of the site, a morphism `w : W ⟶ T` and an
  isomorphism `α : T' ×_T W ≅ V` over `T'` such that `α.hom ≫ q` agrees on the two projections
  of `(T' ×_T W) ×_W (T' ×_T W)`. -/
theorem isSheaf_fpqc_of_isIndQuasiAffineHom_of_isEffectiveFpqcDescent
    (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS}
    (hUsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U))
    {u : yoneda.obj U ⟶ F}
    (hus : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (hue : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (hAPK : ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ (U V : BigFppfOver B S hS) (u : yoneda.obj U ⟶ F) (q : V ⟶ U) (p : V ⟶ T')
      (c : yoneda.obj T' ⟶ F), IsPullback (yoneda.map q) (yoneda.map p) u c →
      Surjective ((BigFppfOver.toScheme B S hS).map p) →
      Etale ((BigFppfOver.toScheme B S hS).map p) →
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) →
      IsIndQuasiAffineHom ((BigFppfOver.toScheme B S hS).map p) →
      yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (α : pullback f w ≅ V),
        α.hom ≫ p = pullback.fst f w ∧
        pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
          pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine hF.isSheaf_fpqc_of_isSheafFor_singleton_affine
    fun {Y T} f hYaff hTaff hsurj hflat hqc ↦ ?_
  exact hF.isSheafFor_singleton_of_isEffectiveFpqcDescent_of_atlas f hsurj hflat hqc
    hUsep hus hue (hAPK Y T f hYaff hTaff hsurj hflat hqc)

end IsAlgebraicSpace

end AlgebraicGeometry

end
