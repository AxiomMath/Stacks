module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Colimits of schemes that remain colimits of algebraic spaces

Let `D` be a diagram in the big fppf site of a scheme `S` and let `c` be a cocone on `D` whose
image under the forgetful functor to schemes is a colimit. Under three further hypotheses --
the diagram covers the colimit on points, étale base change preserves the colimit, and every
compatible cartesian family of separated étale objects over `D` descends to an étale object
over `c.pt` -- the cocone `c` is a colimit in the much larger category of algebraic spaces over
`S`: every compatible family of maps from the `D.obj i` to an algebraic space `F` factors
uniquely through `c.pt`.

## Main results

* `AlgebraicGeometry.Space.isColimit_algebraicSpaces_of_scheme`: **Stacks 07SX**, the universal
  property of the scheme colimit against every algebraic space over `S`.

## Implementation notes

A compatible family of étale objects over the diagram is recorded as a diagram `E` together
with a cartesian natural transformation `E ⟶ D`; its descent is a natural transformation to a
constant diagram whose component squares are cartesian. The conclusion is stated for the Yoneda
images of the cocone legs, so it carries both the existence and the uniqueness of the induced
morphism to an algebraic space.

The proof chooses a separated surjective étale atlas `W ⟶ F` of the target algebraic space,
pulls the family of maps `a i` back along it to obtain a cartesian family over `D`, descends
that family to an étale `U ⟶ c.pt` by hypothesis, and identifies `F` as the coequalizer of the
kernel pair of `U ⟶ c.pt` using Stacks 0262.

## References

* [Stacks Project, Tag 07SX](https://stacks.math.columbia.edu/tag/07SX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

/-- Pulling a compatible family of maps `yoneda.obj (D.obj i) ⟶ F` back along a map
`yoneda.obj W ⟶ F` produces a diagram `E` over the same index category, a cartesian natural
transformation `E ⟶ D`, and a natural transformation `E ⟶ const W` whose component squares are
cartesian.  Existence of the pullbacks is representability of the diagonal of `F`. -/
private theorem exists_cartesian_atlas_pullback_diagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (D : I ⥤ BigFppfOver B S hS)
    (a : ∀ i, yoneda.obj (D.obj i) ⟶ F)
    (ha : ∀ {i j} (f : i ⟶ j), yoneda.map (D.map f) ≫ a j = a i)
    (W : BigFppfOver B S hS) (w : yoneda.obj W ⟶ F) :
    ∃ (E : I ⥤ BigFppfOver B S hS)
      (p : E ⟶ D) (q : E ⟶ (Functor.const I).obj W),
      (∀ {i j : I} (f : i ⟶ j),
        IsPullback (E.map f) (p.app i) (p.app j) (D.map f)) ∧
      ∀ i, IsPullback (yoneda.map (p.app i)) (yoneda.map (q.app i)) (a i) w := by
  classical
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let H (i : I) :=
    (Functor.relativelyRepresentable.diag_iff).1 hF.diagonal_representable (a i)
  let pp (i : I) := (H i).fst' w
  let qq (i : I) := (H i).snd w
  have hpq (i : I) : yoneda.map (pp i) ≫ a i = yoneda.map (qq i) ≫ w := by
    simpa [pp, qq] using (H i).w w
  have hcomp {i j : I} (f : i ⟶ j) :
      yoneda.map (pp i ≫ D.map f) ≫ a j = yoneda.map (qq i) ≫ w := by
    rw [Functor.map_comp, Category.assoc, ha f, hpq]
  let emap {i j : I} (f : i ⟶ j) : (H i).pullback w ⟶ (H j).pullback w :=
    (H j).lift (yoneda.map (pp i ≫ D.map f)) (qq i) (hcomp f)
  have emap_fst {i j : I} (f : i ⟶ j) :
      yoneda.map (emap f) ≫ (H j).fst w = yoneda.map (pp i ≫ D.map f) :=
    (H j).lift_fst (yoneda.map (pp i ≫ D.map f)) (qq i) (hcomp f)
  have emap_snd {i j : I} (f : i ⟶ j) : emap f ≫ qq j = qq i :=
    (H j).lift_snd (yoneda.map (pp i ≫ D.map f)) (qq i) (hcomp f)
  let E : I ⥤ BigFppfOver B S hS := {
    obj i := (H i).pullback w
    map f := emap f
    map_id i := by
      apply (H i).hom_ext
      · simpa [pp, (H i).map_fst'] using emap_fst (𝟙 i)
      · simpa using emap_snd (𝟙 i)
    map_comp {i j k} (f : i ⟶ j) (g : j ⟶ k) := by
      apply (H k).hom_ext
      · calc
          yoneda.map (emap (f ≫ g)) ≫ (H k).fst w =
              yoneda.map (pp i ≫ D.map (f ≫ g)) := emap_fst (f ≫ g)
          _ = yoneda.map (pp i) ≫ yoneda.map (D.map f) ≫ yoneda.map (D.map g) := by
            simp [Functor.map_comp]
          _ = yoneda.map (emap f ≫ emap g) ≫ (H k).fst w := by
            simp only [Functor.map_comp]
            rw [Category.assoc, emap_fst g]
            simp only [Functor.map_comp]
            rw [(H j).map_fst']
            conv_rhs => rw [← Category.assoc]
            rw [emap_fst f]
            simp only [Functor.map_comp, Category.assoc]
      · calc
          emap (f ≫ g) ≫ qq k = qq i := emap_snd (f ≫ g)
          _ = (emap f ≫ emap g) ≫ qq k := by
            rw [Category.assoc, emap_snd g, emap_snd f]
  }
  let p : E ⟶ D := {
    app := pp
    naturality := by
      intro i j f
      apply yoneda.map_injective
      rw [Functor.map_comp, (H j).map_fst']
      exact emap_fst f }
  let q : E ⟶ (Functor.const I).obj W := { app := qq, naturality := fun _ _ f => emap_snd f }
  have hcart {i j : I} (f : i ⟶ j) :
      IsPullback (E.map f) (p.app i) (p.app j) (D.map f) := by
    refine IsPullback.mk' (p.naturality f) ?_ ?_
    · intro T φ ψ h₁ h₂
      have hqnat : E.map f ≫ q.app j = q.app i := by simp
      have hq : φ ≫ q.app i = ψ ≫ q.app i := by
        calc
          φ ≫ q.app i = φ ≫ E.map f ≫ q.app j := by rw [← hqnat]
          _ = ψ ≫ E.map f ≫ q.app j := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ q.app j) h₁
          _ = ψ ≫ q.app i := by rw [hqnat]
      apply (H i).hom_ext
      · simpa [p, pp, Functor.map_comp, (H i).map_fst'] using congrArg yoneda.map h₂
      · simpa [q, qq] using hq
    · intro T a' b' hab
      have hi : yoneda.map b' ≫ a i = yoneda.map (a' ≫ q.app j) ≫ w := by
        calc
          yoneda.map b' ≫ a i = yoneda.map (b' ≫ D.map f) ≫ a j := by
            rw [← ha f]
            simp [Functor.map_comp, Category.assoc]
          _ = yoneda.map (a' ≫ p.app j) ≫ a j := by rw [hab]
          _ = yoneda.map (a' ≫ q.app j) ≫ w := by
            calc
              yoneda.map (a' ≫ p.app j) ≫ a j =
                  yoneda.map a' ≫ (yoneda.map (p.app j) ≫ a j) := by
                    rw [Functor.map_comp, Category.assoc]
              _ = yoneda.map a' ≫ (yoneda.map (q.app j) ≫ w) := by rw [hpq j]
              _ = yoneda.map (a' ≫ q.app j) ≫ w := by
                    rw [Functor.map_comp, Category.assoc]
      let l := (H i).lift (yoneda.map b') (a' ≫ q.app j) hi
      have hlp : l ≫ p.app i = b' := by
        apply yoneda.map_injective
        calc
          yoneda.map (l ≫ p.app i) = yoneda.map l ≫ (H i).fst w := by
            simp [Functor.map_comp, p, pp, (H i).map_fst']
          _ = yoneda.map b' := by
            simp [l]
      have hlq : l ≫ q.app i = a' ≫ q.app j :=
        (H i).lift_snd (yoneda.map b') (a' ≫ q.app j) hi
      have hle : l ≫ E.map f = a' := by
        apply (H j).hom_ext
        · have hproj : l ≫ E.map f ≫ p.app j = a' ≫ p.app j := by
            calc
              l ≫ E.map f ≫ p.app j = l ≫ p.app i ≫ D.map f := by
                simp [p.naturality]
              _ = b' ≫ D.map f := by
                simpa only [Category.assoc] using congrArg (fun t => t ≫ D.map f) hlp
              _ = a' ≫ p.app j := hab.symm
          simpa [Functor.map_comp, Category.assoc, p, pp, (H j).map_fst'] using
            congrArg yoneda.map hproj
        · calc
            l ≫ E.map f ≫ q.app j = l ≫ q.app i := by
              simp [q.naturality]
            _ = a' ≫ q.app j := hlq
      exact ⟨l, hle, hlp⟩
  refine ⟨E, p, q, hcart, ?_⟩
  intro i
  simpa [p, pp, q, qq, (H i).map_fst'] using (H i).isPullback w

/-- Separatedness of a morphism of presheaves on the big fppf site of `S` is unchanged by
precomposition with an isomorphism: the two relative diagonals are isomorphic in the arrow
category. -/
private theorem separated_precomp_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y)
    (hf : IsSeparated B S hS f) :
    IsSeparated B S hS (e.hom ≫ f) := by
  let Q := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.presheaf
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) Q)
  change P (pullback.diagonal f) at hf
  change P (pullback.diagonal (e.hom ≫ f))
  let αhom : pullback (e.hom ≫ f) (e.hom ≫ f) ⟶ pullback f f :=
    pullback.lift
      (pullback.fst (e.hom ≫ f) (e.hom ≫ f) ≫ e.hom)
      (pullback.snd (e.hom ≫ f) (e.hom ≫ f) ≫ e.hom)
      (by simpa [Category.assoc] using
        (pullback.condition (f := e.hom ≫ f) (g := e.hom ≫ f)))
  let αinv : pullback f f ⟶ pullback (e.hom ≫ f) (e.hom ≫ f) :=
    pullback.lift (pullback.fst f f ≫ e.inv) (pullback.snd f f ≫ e.inv)
      (by simpa [Category.assoc] using (pullback.condition (f := f) (g := f)))
  have αhom_fst : αhom ≫ pullback.fst f f =
      pullback.fst (e.hom ≫ f) (e.hom ≫ f) ≫ e.hom := pullback.lift_fst _ _ _
  have αhom_snd : αhom ≫ pullback.snd f f =
      pullback.snd (e.hom ≫ f) (e.hom ≫ f) ≫ e.hom := pullback.lift_snd _ _ _
  have αinv_fst : αinv ≫ pullback.fst (e.hom ≫ f) (e.hom ≫ f) =
      pullback.fst f f ≫ e.inv := pullback.lift_fst _ _ _
  have αinv_snd : αinv ≫ pullback.snd (e.hom ≫ f) (e.hom ≫ f) =
      pullback.snd f f ≫ e.inv := pullback.lift_snd _ _ _
  let α : pullback (e.hom ≫ f) (e.hom ≫ f) ≅ pullback f f :=
    ⟨αhom, αinv,
      pullback.hom_ext
        (by rw [Category.assoc, αinv_fst, ← Category.assoc, αhom_fst, Category.assoc,
          e.hom_inv_id, Category.comp_id, Category.id_comp])
        (by rw [Category.assoc, αinv_snd, ← Category.assoc, αhom_snd, Category.assoc,
          e.hom_inv_id, Category.comp_id, Category.id_comp]),
      pullback.hom_ext
        (by rw [Category.assoc, αhom_fst, ← Category.assoc, αinv_fst, Category.assoc,
          e.inv_hom_id, Category.comp_id, Category.id_comp])
        (by rw [Category.assoc, αhom_snd, ← Category.assoc, αinv_snd, Category.assoc,
          e.inv_hom_id, Category.comp_id, Category.id_comp])⟩
  have hdiag : pullback.diagonal (e.hom ≫ f) ≫ αhom = e.hom ≫ pullback.diagonal f :=
    pullback.hom_ext
      (by rw [Category.assoc, αhom_fst, ← Category.assoc, pullback.diagonal_fst,
        Category.id_comp, Category.assoc, pullback.diagonal_fst, Category.comp_id])
      (by rw [Category.assoc, αhom_snd, ← Category.assoc, pullback.diagonal_snd,
        Category.id_comp, Category.assoc, pullback.diagonal_snd, Category.comp_id])
  let hArrow : Arrow.mk (pullback.diagonal (e.hom ≫ f)) ≅
      Arrow.mk (pullback.diagonal f) := Arrow.isoMk e α hdiag.symm
  exact (MorphismProperty.arrow_mk_iso_iff P hArrow).mpr hf


/-- A surjective étale morphism of the big fppf site of `S` exhibits its target as the
coequalizer of its kernel pair in algebraic spaces: a map to an algebraic space `F` which
identifies the two projections of the kernel pair descends uniquely along it.  This is Stacks
0262 part (3) transported to the sheaf category. -/
private theorem existsUnique_desc_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hfS : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hfE : Etale ((BigFppfOver.toScheme B S hS).map f))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (g : yoneda.obj X ⟶ F)
    (hg : yoneda.map (pullback.fst f f) ≫ g =
      yoneda.map (pullback.snd f f) ≫ g) :
    ∃! b : yoneda.obj Y ⟶ F, yoneda.map f ≫ b = g := by
  classical
  let Q := BigFppfOver.toScheme B S hS
  let PS := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let PE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : PS.IsStableUnderBaseChange := ⟨fun hs hg =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Surjective.{u} : MorphismProperty Scheme.{u})) (hs.map Q) hg⟩
  let : PE.IsStableUnderBaseChange := ⟨fun hs hg =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Etale.{u} : MorphismProperty Scheme.{u})) (hs.map Q) hg⟩
  have hsurj : PS.presheaf (yoneda.map f) :=
    (MorphismProperty.relative_map_iff (P := PS) (F := yoneda)).2 hfS
  have hetale : PE.presheaf (yoneda.map f) :=
    (MorphismProperty.relative_map_iff (P := PE) (F := yoneda)).2 hfE
  let R := pullback f f
  let s := pullback.fst f f
  let t := pullback.snd f f
  have hR : IsPullback (yoneda.map s) (yoneda.map t)
      (yoneda.map f) (yoneda.map f) :=
    (IsPullback.of_hasPullback f f).map yoneda
  let hYspace := isAlgebraicSpace_yoneda B S hS Y
  obtain ⟨hRsh, hXsh, hcol⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS (yoneda.map f) s t hR
      hYspace hsurj hetale
  let J := BigFppfOver.topology B S hS
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let XF : Sheaf J (Type u) := ⟨yoneda.obj X, hXsh⟩
  let YF : Sheaf J (Type u) := ⟨yoneda.obj Y, hYspace.isSheaf⟩
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let sf : RF ⟶ XF := ⟨yoneda.map s⟩
  let tf : RF ⟶ XF := ⟨yoneda.map t⟩
  let ff : XF ⟶ YF := ⟨yoneda.map f⟩
  have hcomm : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hR.w
  obtain ⟨hcol⟩ : Nonempty (IsColimit (Cofork.ofπ ff hcomm)) := by
    simpa [J, RF, XF, YF, sf, tf, ff] using hcol
  let gSheaf : XF ⟶ FF := ⟨g⟩
  let cG : Cofork sf tf := Cofork.ofπ gSheaf (Sheaf.hom_ext hg)
  let bSheaf : YF ⟶ FF := hcol.desc cG
  have hfac : ff ≫ bSheaf = gSheaf := hcol.fac cG WalkingParallelPair.one
  refine ⟨bSheaf.hom, by simpa [ff, gSheaf] using congrArg (·.hom) hfac, fun b' hb' => ?_⟩
  let b'Sheaf : YF ⟶ FF := ⟨b'⟩
  have hb'Sheaf : ff ≫ b'Sheaf = gSheaf := Sheaf.hom_ext hb'
  have hSheafEq : bSheaf = b'Sheaf := Cofork.IsColimit.hom_ext hcol (hfac.trans hb'Sheaf.symm)
  exact (congrArg (·.hom) hSheafEq).symm

/-- A surjective étale morphism of the big fppf site of `S` is an epimorphism against algebraic
spaces: two maps out of its target agreeing after precomposition with it are equal. -/
private theorem cancel_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hfS : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hfE : Etale ((BigFppfOver.toScheme B S hS).map f))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {g₁ g₂ : yoneda.obj Y ⟶ F}
    (h : yoneda.map f ≫ g₁ = yoneda.map f ≫ g₂) : g₁ = g₂ := by
  have hk : yoneda.map (pullback.fst f f) ≫ (yoneda.map f ≫ g₁) =
      yoneda.map (pullback.snd f f) ≫ (yoneda.map f ≫ g₁) := by
    simpa only [← Category.assoc, ← Functor.map_comp] using
      congrArg (fun t => yoneda.map t ≫ g₁) (pullback.condition (f := f) (g := f))
  obtain ⟨_, _, hu⟩ := existsUnique_desc_of_surjective_etale
    B S hS f hfS hfE hF (yoneda.map f ≫ g₁) hk
  exact (hu g₁ rfl).trans (hu g₂ h.symm).symm

/-- A cocone in the big fppf site whose image in schemes is a colimit is itself a colimit. -/
private theorem isColimit_of_scheme_colimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cocone D)
    (hc : IsColimit ((BigFppfOver.toScheme B S hS).mapCocone c)) :
    Nonempty (IsColimit c) :=
  ⟨{ desc := fun s => Over.homMk
        (B.inclusion.preimage (hc.desc ((BigFppfOver.toScheme B S hS).mapCocone s)))
        (B.inclusion.map_injective (by
          rw [Functor.map_comp, Functor.map_preimage]
          refine hc.hom_ext fun i => ?_
          rw [reassoc_of% (hc.fac ((BigFppfOver.toScheme B S hS).mapCocone s) i)]
          exact congrArg B.inclusion.map ((Over.w (s.ι.app i)).trans (Over.w (c.ι.app i)).symm)))
     fac := fun s i => by
        apply Over.OverMorphism.ext
        apply B.inclusion.map_injective
        change (BigFppfOver.toScheme B S hS).map (c.ι.app i) ≫ B.inclusion.map
          (B.inclusion.preimage _) = (BigFppfOver.toScheme B S hS).map (s.ι.app i)
        rw [Functor.map_preimage]
        exact hc.fac _ i
     uniq := fun s m hm => by
        apply Over.OverMorphism.ext
        apply B.inclusion.map_injective
        change _ = B.inclusion.map (B.inclusion.preimage _)
        rw [Functor.map_preimage]
        exact hc.uniq ((BigFppfOver.toScheme B S hS).mapCocone s)
          ((BigFppfOver.toScheme B S hS).map m) fun i =>
            ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
              (congrArg (BigFppfOver.toScheme B S hS).map (hm i)) }⟩

/-- If the scheme image of a cocone is a colimit, the cocone is jointly epimorphic against every
algebraic space: two maps out of its vertex agreeing on every leg are equal.  Equality is
obtained by factoring the vertex through the fibre product of the two maps, whose existence is
representability of the diagonal. -/
private theorem maps_equal_of_scheme_colimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cocone D)
    (hc : IsColimit ((BigFppfOver.toScheme B S hS).mapCocone c))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (a b : yoneda.obj c.pt ⟶ F)
    (hab : ∀ i, yoneda.map (c.ι.app i) ≫ a = yoneda.map (c.ι.app i) ≫ b) :
    a = b := by
  classical
  let H := (Functor.relativelyRepresentable.diag_iff).1
    hF.diagonal_representable a
  let K := H.pullback b
  let fst := H.fst' b
  let snd := H.snd b
  have hfstMap : yoneda.map fst = H.fst b := yoneda.map_preimage _
  let ellApp (i : I) : D.obj i ⟶ K :=
    H.lift (yoneda.map (c.ι.app i)) (c.ι.app i) (hab i)
  have ellFst (i : I) : yoneda.map (ellApp i) ≫ H.fst b = yoneda.map (c.ι.app i) :=
    H.lift_fst (yoneda.map (c.ι.app i)) (c.ι.app i) (hab i)
  have ellSnd (i : I) : ellApp i ≫ snd = c.ι.app i :=
    H.lift_snd (yoneda.map (c.ι.app i)) (c.ι.app i) (hab i)
  let ell : D ⟶ (Functor.const I).obj K := {
    app := ellApp
    naturality := by
      intro i j f
      apply H.hom_ext
      · calc
          yoneda.map (D.map f ≫ ellApp j) ≫ H.fst b =
              yoneda.map (D.map f) ≫ yoneda.map (ellApp j) ≫ H.fst b := by
                simp [Functor.map_comp, Category.assoc]
          _ = yoneda.map (D.map f) ≫ yoneda.map (c.ι.app j) := by rw [ellFst]
          _ = yoneda.map (c.ι.app i) := by rw [← Functor.map_comp, c.w f]
          _ = yoneda.map (ellApp i) ≫ H.fst b := (ellFst i).symm
      · calc
          D.map f ≫ ellApp j ≫ snd = D.map f ≫ c.ι.app j := by rw [ellSnd]
          _ = c.ι.app i := c.w f
          _ = ellApp i ≫ snd := (ellSnd i).symm }
  let cK : Cocone D := { pt := K, ι := ell }
  obtain ⟨hc'⟩ := isColimit_of_scheme_colimit B S hS D c hc
  let mOver : c.pt ⟶ K := hc'.desc cK
  have key {k : K ⟶ c.pt} (hk : ∀ i, ellApp i ≫ k = c.ι.app i) : mOver ≫ k = 𝟙 c.pt :=
    hc'.hom_ext fun i => (hc'.fac_assoc cK i k).trans ((hk i).trans (Category.comp_id _).symm)
  have hfstOver : mOver ≫ fst = 𝟙 c.pt :=
    key fun i => yoneda.map_injective (by simpa [Functor.map_comp, hfstMap] using ellFst i)
  have hsndOver : mOver ≫ snd = 𝟙 c.pt := key ellSnd
  calc
    a = yoneda.map (mOver ≫ fst) ≫ a := by simp [hfstOver]
    _ = yoneda.map (mOver ≫ snd) ≫ b := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hfstMap,
        (H.isPullback b).w]
    _ = b := by simp [hsndOver]

/-- Under descent of separated étale families and preservation of the scheme
colimit by étale base change, the colimit is also a colimit of algebraic spaces. -/
@[stacks 07SX]
public theorem isColimit_algebraicSpaces_of_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cocone D)
    (_hColimit : IsColimit ((BigFppfOver.toScheme B S hS).mapCocone c))
    (hCover : ∀ x : (BigFppfOver.toScheme B S hS).obj c.pt,
      ∃ (i : I) (y : (BigFppfOver.toScheme B S hS).obj (D.obj i)),
        (BigFppfOver.toScheme B S hS).map (c.ι.app i) y = x)
    (hEtaleColimit :
      ∀ (U : BigFppfOver B S hS) (v : U ⟶ c.pt),
        Etale ((BigFppfOver.toScheme B S hS).map v) →
        ∀ (E : I ⥤ BigFppfOver B S hS) (p : E ⟶ D)
          (q : E ⟶ (Functor.const I).obj U),
          (∀ i, IsPullback (p.app i) (q.app i) (c.ι.app i) v) →
          IsColimit ((BigFppfOver.toScheme B S hS).mapCocone
            ({ pt := U, ι := q } : Cocone E)))
    (hEtaleDescent :
      ∀ (E : I ⥤ BigFppfOver B S hS) (p : E ⟶ D),
        (∀ i, Etale ((BigFppfOver.toScheme B S hS).map (p.app i))) →
        (∀ i, _root_.AlgebraicGeometry.IsSeparated
          ((BigFppfOver.toScheme B S hS).map (p.app i))) →
        (∀ {i j : I} (f : i ⟶ j),
          IsPullback (E.map f) (p.app i) (p.app j) (D.map f)) →
        ∃ (U : BigFppfOver B S hS) (v : U ⟶ c.pt)
          (q : E ⟶ (Functor.const I).obj U),
          Etale ((BigFppfOver.toScheme B S hS).map v) ∧
          (∀ i, IsPullback (p.app i) (q.app i) (c.ι.app i) v)) :
    ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B S hS F →
      ∀ (a : ∀ i : I, yoneda.obj (D.obj i) ⟶ F),
        (∀ {i j : I} (f : i ⟶ j), yoneda.map (D.map f) ≫ a j = a i) →
        ∃! b : yoneda.obj c.pt ⟶ F,
          ∀ i, yoneda.map (c.ι.app i) ≫ b = a i := by
  classical
  intro F hF a ha
  let Q := BigFppfOver.toScheme B S hS
  obtain ⟨W, w, J, Y, e, hwsurj, hwetale, hYaff, _⟩ :=
    exists_etale_surjective_coproduct_affine_cover B S hS F hF
  have hWsep : Scheme.IsSeparated (Q.obj W) := by
    have hArrow : Arrow.mk (terminal.from (∐ Y)) ≅ Arrow.mk (terminal.from (Q.obj W)) :=
      Arrow.isoMk e (Iso.refl _) (by apply terminal.hom_ext)
    let : Scheme.IsSeparated (∐ Y) := isSeparated_sigma_of_isAffine Y hYaff
    have hYsep : _root_.AlgebraicGeometry.IsSeparated (terminal.from (∐ Y)) := inferInstance
    exact ⟨(MorphismProperty.arrow_mk_iso_iff
      (P := @_root_.AlgebraicGeometry.IsSeparated.{u}) hArrow).mp hYsep⟩
  have hwEtale : IsEtale B S hS w := isEtale_of_presheaf_etale B S hS hwetale
  have hwSeparated : IsSeparated B S hS w :=
    isSeparated_of_isEtale_of_scheme_isSeparated
      B S hS F hF W hWsep w hwEtale
  obtain ⟨E, p, q, hcart, hpull⟩ :=
    exists_cartesian_atlas_pullback_diagram B S hS hF D a ha W w
  have hpEtale : ∀ i, Etale (Q.map (p.app i)) := fun i =>
    MorphismProperty.relative.property hwetale (a i) (yoneda.map (q.app i))
      (p.app i) ((hpull i).flip)
  have hpSurjective : ∀ i, Surjective (Q.map (p.app i)) := fun i =>
    MorphismProperty.relative.property hwsurj (a i) (yoneda.map (q.app i))
      (p.app i) ((hpull i).flip)
  have hpSeparated : ∀ i, _root_.AlgebraicGeometry.IsSeparated (Q.map (p.app i)) := by
    intro i
    have hcanonical : IsSeparated B S hS (pullback.snd w (a i)) :=
      isSeparated_pullbackSnd B S hS (a i) hwSeparated
    have hflip := (hpull i).flip
    let ePB := hflip.isoPullback
    have hsepYon : IsSeparated B S hS (ePB.hom ≫ pullback.snd w (a i)) :=
      separated_precomp_iso B S hS ePB (pullback.snd w (a i)) hcanonical
    have hpbEq : ePB.hom ≫ pullback.snd w (a i) = yoneda.map (p.app i) :=
      hflip.isoPullback_hom_snd
    rw [hpbEq] at hsepYon
    exact (isSeparated_yoneda_map_iff B S hS (p.app i)).1 hsepYon
  obtain ⟨U, v, r, hvEtale, hsq⟩ :=
    hEtaleDescent E p hpEtale hpSeparated hcart
  let cE : Cocone E := { pt := U, ι := r }
  have hEcol : IsColimit (Q.mapCocone cE) :=
    hEtaleColimit U v hvEtale E p r hsq
  let cW : Cocone E := { pt := W, ι := q }
  obtain ⟨hEcol'⟩ := isColimit_of_scheme_colimit B S hS E cE hEcol
  let h : U ⟶ W := hEcol'.desc cW
  let g : yoneda.obj U ⟶ F := yoneda.map h ≫ w
  have hrh (i : I) : r.app i ≫ h = q.app i := hEcol'.fac cW i
  have hrestrict : ∀ i, yoneda.map (r.app i) ≫ g = yoneda.map (p.app i) ≫ a i := by
    intro i
    calc
      yoneda.map (r.app i) ≫ g = yoneda.map (r.app i ≫ h) ≫ w := by
        simp [g, Functor.map_comp, Category.assoc]
      _ = yoneda.map (q.app i) ≫ w := by rw [hrh i]
      _ = yoneda.map (p.app i) ≫ a i := (hpull i).w.symm
  have hvSurjective : Surjective (Q.map v) := by
    constructor
    intro x
    obtain ⟨i, y, rfl⟩ := hCover x
    obtain ⟨z, rfl⟩ := (hpSurjective i).surj y
    have hsqY : Q.map (p.app i) ≫ Q.map (c.ι.app i) = Q.map (r.app i) ≫ Q.map v := by
      simpa [Functor.map_comp] using congrArg Q.map (hsq i).w
    refine ⟨Q.map (r.app i) z, ?_⟩
    calc
      Q.map v (Q.map (r.app i) z) = (Q.map (r.app i) ≫ Q.map v) z := rfl
      _ = (Q.map (p.app i) ≫ Q.map (c.ι.app i)) z := by rw [← hsqY]
      _ = Q.map (c.ι.app i) (Q.map (p.app i) z) := rfl
  let R := pullback v v
  let s := pullback.fst v v
  let t := pullback.snd v v
  have hRpb : IsPullback s t v v := IsPullback.of_hasPullback v v
  let vR := t ≫ v
  have htEtale : Etale (Q.map t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hRpb.map Q) hvEtale
  have hvREtale : Etale (Q.map vR) := by
    rw [Q.map_comp]
    let : Etale (Q.map t) := htEtale
    let : Etale (Q.map v) := hvEtale
    infer_instance
  let cR := (Functor.const I).map vR
  let E₂ := pullback c.ι cR
  let p₂ := pullback.fst c.ι cR
  let q₂ := pullback.snd c.ι cR
  have hbasePB : IsPullback p₂ q₂ c.ι cR := IsPullback.of_hasPullback c.ι cR
  have hsquares₂ : ∀ i, IsPullback (p₂.app i) (q₂.app i) (c.ι.app i) vR := by
    intro i
    let ev := (evaluation I (BigFppfOver B S hS)).obj i
    have hEval := Functor.map_isPullback ev hbasePB
    simpa [ev, E₂, p₂, q₂, cR, vR, Functor.const_map_app,
      Functor.const_obj_obj, evaluation_obj_map] using hEval
  let c₂ : Cocone E₂ := { pt := R, ι := q₂ }
  have h₂col : IsColimit (Q.mapCocone c₂) :=
    hEtaleColimit R vR hvREtale E₂ p₂ q₂ hsquares₂
  have hstage₂ : ∀ i, yoneda.map (q₂.app i) ≫ (yoneda.map s ≫ g) =
      yoneda.map (q₂.app i) ≫ (yoneda.map t ≫ g) := by
    intro i
    have hw : p₂.app i ≫ c.ι.app i = q₂.app i ≫ t ≫ v := (hsquares₂ i).w
    have hcond₁ : p₂.app i ≫ c.ι.app i = (q₂.app i ≫ s) ≫ v := by
      rw [hw, Category.assoc, hRpb.w]
    have hcond₂ : p₂.app i ≫ c.ι.app i = (q₂.app i ≫ t) ≫ v := by rw [hw, Category.assoc]
    have key (l : E₂.obj i ⟶ E.obj i) (hl : l ≫ p.app i = p₂.app i) :
        yoneda.map (l ≫ r.app i) ≫ g = yoneda.map (p₂.app i) ≫ a i := by
      rw [Functor.map_comp, Category.assoc, hrestrict i, ← Category.assoc, ← Functor.map_comp, hl]
    have h₁ := key _ ((hsq i).lift_fst (p₂.app i) (q₂.app i ≫ s) hcond₁)
    have h₂ := key _ ((hsq i).lift_fst (p₂.app i) (q₂.app i ≫ t) hcond₂)
    rw [(hsq i).lift_snd (p₂.app i) (q₂.app i ≫ s) hcond₁] at h₁
    rw [(hsq i).lift_snd (p₂.app i) (q₂.app i ≫ t) hcond₂] at h₂
    simpa [Functor.map_comp, Category.assoc] using h₁.trans h₂.symm
  have hKernel : yoneda.map s ≫ g = yoneda.map t ≫ g :=
    maps_equal_of_scheme_colimit B S hS E₂ c₂ h₂col hF
      (yoneda.map s ≫ g) (yoneda.map t ≫ g) hstage₂
  obtain ⟨b, hb, hbUnique⟩ :=
    existsUnique_desc_of_surjective_etale B S hS v hvSurjective hvEtale hF g hKernel
  refine ⟨b, fun i => ?_, fun b' hb' => hbUnique b' ?_⟩
  · refine cancel_of_surjective_etale B S hS (p.app i) (hpSurjective i) (hpEtale i) hF ?_
    rw [← Category.assoc, ← Functor.map_comp, (hsq i).w, Functor.map_comp, Category.assoc, hb,
      hrestrict]
  · refine maps_equal_of_scheme_colimit B S hS E cE hEcol hF _ g fun i => ?_
    change yoneda.map (r.app i) ≫ yoneda.map v ≫ b' = yoneda.map (r.app i) ≫ g
    rw [← Category.assoc, ← Functor.map_comp, ← (hsq i).w, Functor.map_comp, Category.assoc,
      hb' i, hrestrict]

end Space

end AlgebraicGeometry

end
