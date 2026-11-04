module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.TransportedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Separatedness of a morphism descends to a stage of a limit

Let `B = lim B_i` be the limit of a directed inverse system of algebraic spaces over `S` with
affine transition morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism over `B₀` of quasi-compact and
quasi-separated algebraic spaces, `B₀` itself being quasi-compact and quasi-separated (the
situation of Stacks 084W), and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base changes of `f₀` to
`B_i` and to `B`. Stacks 0851 asserts that if `f` is separated then so is some `f_i`.

Here the system of bases satisfies the chapter's standing convention of Section 70.2 (tag 07SD,
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`), and nothing is asked of the size of its
index set.

## Main results

* `AlgebraicGeometry.Space.exists_isSeparated_pullbackMap_of_siteContainsBaseChangeLimits`: if the
  base change of `f₀` to the limit is separated, then so is its base change to some stage.

## References

* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Separatedness transfers along a commuting square whose horizontal arrows are isomorphisms. -/
private theorem isSeparated_of_conj_iso {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (f' : F' ⟶ G') (e : F ≅ F') (e' : G ≅ G') (w : f ≫ e'.hom = e.hom ≫ f')
    (hf : IsSeparated B S hS f) : IsSeparated B S hS f' := by
  have : f' = e.inv ≫ f ≫ e'.hom := by rw [w, Iso.inv_hom_id_assoc]
  rw [this]
  exact isSeparated_comp B S hS _ _ (@isSeparated_of_isIso B S hS _ _ _ (Iso.isIso_inv _))
    (isSeparated_comp B S hS _ _ hf (@isSeparated_of_isIso B S hS _ _ _ (Iso.isIso_hom _)))

/-- **Stacks 0851.** In the situation of Stacks 084W, if the base change `f : X ⟶ Y` of
`f₀ : X₀ ⟶ Y₀` to the limit `B = lim B_i` is separated, then the base change `f_i : X_i ⟶ Y_i` of
`f₀` to some stage `B_i` with `i ≥ 0` is separated. -/
@[stacks 0851 "under the chapter's convention of Section 70.2 (tag 07SD) on the system of \
bases, every stage quasi-compact; proved in an enlarged site"]
theorem exists_isSeparated_pullbackMap_of_siteContainsBaseChangeLimits {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (base : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hbase : ∀ i, IsAlgebraicSpace B S hS (base.obj i))
    (hAffine : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a))
    (hconv : SiteContainsBaseChangeLimits B S hS base)
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (base.obj i)) (i₀ : I)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X₀ ⟶ base.obj (op i₀))
    (q : Y₀ ⟶ base.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ q = p)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hB₀qs : IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op i₀)))
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (hY₀qc : IsQuasiCompactSpace B S hS Y₀) (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (hf : IsSeparated B S hS (pullback.map (limit.π base (op i₀)) p (limit.π base (op i₀)) q
      (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsSeparated B S hS (pullback.map (base.map (homOfLE hi).op) p
      (base.map (homOfLE hi).op) q (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  classical
  have hB₀qc := hQc (op i₀)
  obtain ⟨B', h, hSize', hHomSize', eL, heL⟩ := exists_changeBigSite_limit_iso B S hS base hbase
    hAffine hconv hQc
  let hS' : B'.Contains S := largerContains h hS
  let hZ' : B'.Contains (⊤_ Scheme.{u}) := largerContains h hZ
  have : ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z),
      HasPullback f g := fun _ _ => inferInstance
  have : ∀ {X Y Z : (BigFppfOver B' S hS')ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z),
      HasPullback f g := fun _ _ => inferInstance
  let G := changeBigSite B B' h S hS
  let Da := ObjectProperty.lift _ base hbase
  let D' := changeBigSiteSystem B B' h S hS Da
  have hL := isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS base hconv hbase
    hAffine hQc
  let La : AlgebraicSpaces B S hS := ⟨limit base, hL⟩
  have hcomp : ∀ {X Y W : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ W),
      (G.map a).hom ≫ (G.map b).hom = (G.map (a ≫ b)).hom :=
    fun a b => (congrArg (fun k => k.hom) (G.map_comp a b)).symm
  let X₀a : AlgebraicSpaces B S hS := ⟨X₀, hX₀⟩
  let Y₀a : AlgebraicSpaces B S hS := ⟨Y₀, hY₀⟩
  let pa : X₀a ⟶ Da.obj (op i₀) := ObjectProperty.homMk p
  let qa : Y₀a ⟶ Da.obj (op i₀) := ObjectProperty.homMk q
  let f₀a : X₀a ⟶ Y₀a := ObjectProperty.homMk f₀
  have hf₀a : (G.map f₀a).hom ≫ (G.map qa).hom = (G.map pa).hom :=
    (hcomp f₀a qa).trans (congrArg (fun k => (G.map k).hom) (ObjectProperty.hom_ext _ hf₀))
  let D'sys : MorphismDescentSystem B' S hS' hZ' I :=
    { base := D'
      indexSize := by rwa [Cardinal.mk_congr (Opposite.equivToOpposite (α := I))]
      base_isAlgebraicSpace := fun i => (G.obj (Da.obj (op i))).property
      transition_affine := fun a => isAffineHom_changeBigSite_map B B' h S hS _ (Da.map a)
        (hAffine a)
      limit_isAlgebraicSpace := isAlgebraicSpace_limit B' S hS' D' hSize' hHomSize'
        (fun i => (G.obj (Da.obj i)).property)
        (fun a => isAffineHom_changeBigSite_map B B' h S hS _ (Da.map a) (hAffine a))
      initial := i₀
      source₀ := (G.obj X₀a).obj
      target₀ := (G.obj Y₀a).obj
      sourceToBase := (G.map pa).hom
      targetToBase := (G.map qa).hom
      map₀ := (G.map f₀a).hom
      map₀_over := hf₀a
      source₀_isAlgebraicSpace := (G.obj X₀a).property
      target₀_isAlgebraicSpace := (G.obj Y₀a).property
      base₀_quasiCompact := isQuasiCompactSpace_changeBigSite_obj B B' h S hS
        (X := Da.obj (op i₀)) hB₀qc
      base₀_quasiSeparated := isAbsolutelyQuasiSeparated_changeBigSite_obj B B' h S hS hZ
        (X := Da.obj (op i₀)) hB₀qc hB₀qs
      source₀_quasiCompact := isQuasiCompactSpace_changeBigSite_obj B B' h S hS (X := X₀a) hX₀qc
      source₀_quasiSeparated := isAbsolutelyQuasiSeparated_changeBigSite_obj B B' h S hS hZ
        (X := X₀a) hX₀qc hX₀qs
      target₀_quasiCompact := isQuasiCompactSpace_changeBigSite_obj B B' h S hS (X := Y₀a) hY₀qc
      target₀_quasiSeparated := isAbsolutelyQuasiSeparated_changeBigSite_obj B B' h S hS hZ
        (X := Y₀a) hY₀qc hY₀qs }
  let πa : La ⟶ Da.obj (op i₀) := ObjectProperty.homMk (limit.π base (op i₀))
  let PXa : AlgebraicSpaces B S hS :=
    ⟨pullback (limit.π base (op i₀)) p, isAlgebraicSpace_pullback B S hS _ _ hL hX₀ (hbase _)⟩
  let PYa : AlgebraicSpaces B S hS :=
    ⟨pullback (limit.π base (op i₀)) q, isAlgebraicSpace_pullback B S hS _ _ hL hY₀ (hbase _)⟩
  let fX : PXa ⟶ La := ObjectProperty.homMk (pullback.fst _ _)
  let sX : PXa ⟶ X₀a := ObjectProperty.homMk (pullback.snd _ _)
  let fY : PYa ⟶ La := ObjectProperty.homMk (pullback.fst _ _)
  let sY : PYa ⟶ Y₀a := ObjectProperty.homMk (pullback.snd _ _)
  let mla : PXa ⟶ PYa := ObjectProperty.homMk (pullback.map (limit.π base (op i₀)) p
    (limit.π base (op i₀)) q (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))
  have hmlf : mla ≫ fY = fX := ObjectProperty.hom_ext _
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
  have hmls : mla ≫ sY = sX ≫ f₀a := ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  have hsqX := isPullback_changeBigSite_map_of_iso B B' h S hS (fst := fX) (snd := sX) (f := πa)
    (g := pa) (IsPullback.of_hasPullback (limit.π base (op i₀)) p) eL (Iso.refl _)
    (limit.π D' (op i₀)) (G.map pa).hom (heL (op i₀)) (Category.id_comp _)
  have hsqY := isPullback_changeBigSite_map_of_iso B B' h S hS (fst := fY) (snd := sY) (f := πa)
    (g := qa) (IsPullback.of_hasPullback (limit.π base (op i₀)) q) eL (Iso.refl _)
    (limit.π D' (op i₀)) (G.map qa).hom (heL (op i₀)) (Category.id_comp _)
  have hconj : (G.map mla).hom ≫ hsqY.isoPullback.hom = hsqX.isoPullback.hom ≫ D'sys.mapLimit := by
    apply pullback.hom_ext
    · rw [Category.assoc, hsqY.isoPullback_hom_fst, ← Category.assoc, hcomp, hmlf]
      exact ((Category.assoc _ _ _).trans ((congrArg (hsqX.isoPullback.hom ≫ ·)
        D'sys.mapLimit_fst).trans hsqX.isoPullback_hom_fst)).symm
    · rw [Category.assoc, hsqY.isoPullback_hom_snd, Iso.refl_hom, Category.comp_id, hcomp, hmls,
        ← hcomp]
      exact ((Category.assoc _ _ _).trans ((congrArg (hsqX.isoPullback.hom ≫ ·)
        D'sys.mapLimit_snd).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (G.map f₀a).hom)
            (hsqX.isoPullback_hom_snd.trans (Category.comp_id _)))))).symm
  have hGml : IsSeparated B' S hS' (G.map mla).hom :=
    isSeparated_changeBigSite_map B B' h S hS mla hf
  have hml' : IsSeparated B' S hS' D'sys.mapLimit :=
    isSeparated_of_conj_iso B' S hS' _ _ hsqX.isoPullback hsqY.isoPullback hconj hGml
  obtain ⟨i, hi, hsep⟩ := D'sys.exists_isSeparated_mapAt_of_isSeparated_mapLimit hml'
  refine ⟨i, hi, ?_⟩
  let ba : Da.obj (op i) ⟶ Da.obj (op i₀) := Da.map (homOfLE hi).op
  let SXa : AlgebraicSpaces B S hS :=
    ⟨pullback (base.map (homOfLE hi).op) p, isAlgebraicSpace_pullback B S hS _ _ (hbase _) hX₀
      (hbase _)⟩
  let SYa : AlgebraicSpaces B S hS :=
    ⟨pullback (base.map (homOfLE hi).op) q, isAlgebraicSpace_pullback B S hS _ _ (hbase _) hY₀
      (hbase _)⟩
  let gX : SXa ⟶ Da.obj (op i) := ObjectProperty.homMk (pullback.fst _ _)
  let tX : SXa ⟶ X₀a := ObjectProperty.homMk (pullback.snd _ _)
  let gY : SYa ⟶ Da.obj (op i) := ObjectProperty.homMk (pullback.fst _ _)
  let tY : SYa ⟶ Y₀a := ObjectProperty.homMk (pullback.snd _ _)
  let mia : SXa ⟶ SYa := ObjectProperty.homMk (pullback.map (base.map (homOfLE hi).op) p
    (base.map (homOfLE hi).op) q (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))
  have hmif : mia ≫ gY = gX := ObjectProperty.hom_ext _
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
  have hmis : mia ≫ tY = tX ≫ f₀a := ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  have hlX := isPullback_changeBigSite_map B B' h S hS (fst := gX) (snd := tX) (f := ba) (g := pa)
    (IsPullback.of_hasPullback (base.map (homOfLE hi).op) p)
  have hlY := isPullback_changeBigSite_map B B' h S hS (fst := gY) (snd := tY) (f := ba) (g := qa)
    (IsPullback.of_hasPullback (base.map (homOfLE hi).op) q)
  have hconj' : (G.map mia).hom ≫ hlY.isoPullback.hom = hlX.isoPullback.hom ≫ D'sys.mapAt i hi := by
    apply pullback.hom_ext
    · rw [Category.assoc, hlY.isoPullback_hom_fst, hcomp, hmif]
      exact ((Category.assoc _ _ _).trans ((congrArg (hlX.isoPullback.hom ≫ ·)
        (D'sys.mapAt_fst i hi)).trans hlX.isoPullback_hom_fst)).symm
    · rw [Category.assoc, hlY.isoPullback_hom_snd, hcomp, hmis, ← hcomp]
      exact ((Category.assoc _ _ _).trans ((congrArg (hlX.isoPullback.hom ≫ ·)
        (D'sys.mapAt_snd i hi)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (G.map f₀a).hom) hlX.isoPullback_hom_snd)))).symm
  have hGmi : IsSeparated B' S hS' (G.map mia).hom :=
    isSeparated_of_conj_iso B' S hS' _ _ hlX.isoPullback.symm hlY.isoPullback.symm
      ((Iso.comp_inv_eq _).mpr (by
      rw [Category.assoc, hconj', Iso.symm_hom]; exact (Iso.inv_hom_id_assoc _ _).symm)) hsep
  exact isSeparated_of_changeBigSite_map B B' h S hS mia hGmi

end AlgebraicGeometry.Space

end
