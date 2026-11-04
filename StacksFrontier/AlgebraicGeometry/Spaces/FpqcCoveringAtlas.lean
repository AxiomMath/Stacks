module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# Recognising an fpqc covering of algebraic spaces on an étale atlas

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `a : U ⟶ X` be a surjective étale morphism from a scheme in the site. A family of
morphisms of algebraic spaces with target `X` is an fpqc covering exactly when the family
pulled back to `U` is an fpqc covering of `U`.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_isoComp`: the fpqc condition is unchanged by
  precomposing each member of a family with an isomorphism.
* `AlgebraicGeometry.Space.isFpqcCovering_iff_pullback_atlas`: a family with target `X` is an
  fpqc covering exactly when its pullback along a surjective étale atlas is.

## References

* [Stacks Project, Tag 03MS](https://stacks.math.columbia.edu/tag/03MS)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fpqc condition of Stacks 03MQ is unchanged by precomposing every member of a family
with an isomorphism. -/
theorem isFpqcCovering_isoComp {I : Type v}
    {X Y : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : ∀ i, X i ⟶ Y i) [∀ i, IsIso (e i)] (g : ∀ i, Y i ⟶ Z)
    (hg : IsFpqcCovering B S hS g) :
    IsFpqcCovering B S hS fun i ↦ e i ≫ g i := by
  refine ⟨fun i ↦ (holdsOnEveryEtaleChart_iso_comp_iff B S hS _ (e i) (g i)).2 (hg.1 i),
    fun T h ↦ ?_⟩
  obtain ⟨V, hfinite, hcover, hfactor⟩ := hg.2 T h
  refine ⟨V, hfinite, hcover, fun j ↦ ?_⟩
  obtain ⟨i, b, hb⟩ := hfactor j
  refine ⟨i, b ≫ inv (e i), ?_⟩
  rwa [Category.assoc, ← Category.assoc (inv (e i)), IsIso.inv_hom_id, Category.id_comp]

/-- A family of morphisms of algebraic spaces over `S` with target `X` is an
fpqc covering exactly when its pullback along a surjective étale morphism `a : U ⟶ X` from a
scheme in the site is an fpqc covering of `U`. -/
@[stacks 03MS]
theorem isFpqcCovering_iff_pullback_atlas
    {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.obj)
    (ha_surj : IsSurjective B S hS a) (ha_etale : IsEtale B S hS a) :
    IsFpqcCovering B S hS (fun i ↦ (f i).hom) ↔
      IsFpqcCovering B S hS (fun i ↦ pullback.fst a (f i).hom) := by
  have ha_rep : yoneda.relativelyRepresentable a :=
    (Functor.relativelyRepresentable.diag_iff
      (F := yoneda) (X := X.obj)).mp X.property.diagonal_representable a
  constructor
  · intro hf
    have hbase : IsFpqcCovering B S hS (fun i ↦ pullback.snd (f i).hom a) :=
      isFpqcCovering_pullback B S hS (fun i ↦ f i)
        (ObjectProperty.homMk a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) ⟶ X) hf
    simpa using isFpqcCovering_isoComp B S hS
      (fun i ↦ (pullbackSymmetry a (f i).hom).hom)
      (fun i ↦ pullback.snd (f i).hom a) hbase
  · intro hf
    have hsurj : (MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a :=
      (surjective_iff_pointsMap_surjective B S hS
        (isAlgebraicSpace_yoneda B S hS U) X.property a ha_rep).mpr ha_surj
    have hetale : (MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a :=
      (isEtale_iff_presheaf_of_yoneda B S hS a).1 ha_etale
    refine ⟨fun i ↦ ?_, fun T h ↦ ?_⟩
    · apply ((isFlat_tfae B S hS (Xi i).property X.property (f i).hom).out 1 5).mpr
      exact ⟨U, a, ha_surj, ha_etale, hf.1 i⟩
    classical
    have hpull_rep : (pullback h a).IsRepresentable := by
      simpa only [yonedaEquiv.symm_apply_apply] using
        (yoneda_relativelyRepresentable_iff_pullback_representable a).mp ha_rep
          ((BigAffineFppf.inclusion B S hS).obj T) (yonedaEquiv h)
    let P := (pullback h a).reprX
    let e : yoneda.obj P ≅ pullback h a := Functor.reprW (pullback h a)
    let pT : P ⟶ (BigAffineFppf.inclusion B S hS).obj T :=
      yoneda.preimage (e.hom ≫ pullback.fst h a)
    let pU : P ⟶ U := yoneda.preimage (e.hom ≫ pullback.snd h a)
    have hpb : IsPullback (yoneda.map pT) (yoneda.map pU) h a :=
      IsPullback.of_iso_pullback
        ⟨by simp only [pT, pU, yoneda.map_preimage, Category.assoc, pullback.condition]⟩
        e (by simp [pT]) (by simp [pU])
    have hpT_surj : Surjective ((BigFppfOver.toScheme B S hS).map pT) :=
      hsurj.2 h (yoneda.map pU) pT hpb.flip
    have hpT_etale : Etale ((BigFppfOver.toScheme B S hS).map pT) :=
      hetale.2 h (yoneda.map pU) pT hpb.flip
    have himages_cover : (Set.univ : Set ((BigAffineFppf.toScheme B S hS).obj T)) ⊆
        ⋃ V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens,
          ((BigFppfOver.toScheme B S hS).map pT).base ''
            (V.1 : Set ((BigFppfOver.toScheme B S hS).obj P)) := by
      intro x _
      obtain ⟨y, hy⟩ := ((BigFppfOver.toScheme B S hS).map pT).surjective x
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
        ((BigFppfOver.toScheme B S hS).obj P).isBasis_affineOpens.mem_nhds_iff.mp
          ((⊤ : ((BigFppfOver.toScheme B S hS).obj P).Opens).isOpen.mem_nhds (by simp))
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, ⟨y, hyV, hy⟩⟩
    obtain ⟨J, -, hJfinite, hJcover⟩ :=
      (isCompact_univ (X := (BigAffineFppf.toScheme B S hS).obj T)).elim_finite_subcover_image
          (b := Set.univ)
          (c := fun V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens ↦
            ((BigFppfOver.toScheme B S hS).map pT).base ''
              (V.1 : Set ((BigFppfOver.toScheme B S hS).obj P)))
          (fun V _ ↦ ((BigFppfOver.toScheme B S hS).map pT).isOpenMap _ V.1.isOpen)
          (by simpa using himages_cover)
    choose jP hjP using fun V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens ↦
      exists_openSiteObject'_hom P V.1
    let Wobj (V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens) :
        BigAffineFppf B S hS := ⟨openSiteObject' P V.1, V.property⟩
    let jT (V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens) : Wobj V ⟶ T :=
      ObjectProperty.homMk (jP V ≫ pT)
    let jU (V : ((BigFppfOver.toScheme B S hS).obj P).affineOpens) :
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (Wobj V)) ⟶ yoneda.obj U :=
      yoneda.map (jP V ≫ pU)
    let O : PreZeroHypercover T := { I₀ := J, X := fun V ↦ Wobj V.1, f := fun V ↦ jT V.1 }
    have hmap (V : J) : (BigAffineFppf.toScheme B S hS).map (O.f V) =
        (V.1).1.ι ≫ (BigFppfOver.toScheme B S hS).map pT := by
      show (BigFppfOver.toScheme B S hS).map (jP V.1 ≫ pT) =
        (V.1).1.ι ≫ (BigFppfOver.toScheme B S hS).map pT
      rw [Functor.map_comp, hjP]
    have hOcover_etale : Presieve.ofArrows
        (fun V ↦ (BigAffineFppf.toScheme B S hS).obj (O.X V))
        (fun V ↦ (BigAffineFppf.toScheme B S hS).map (O.f V)) ∈
          Scheme.etalePrecoverage ((BigAffineFppf.toScheme B S hS).obj T) := by
      rw [Scheme.etalePrecoverage,
        Scheme.ofArrows_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})]
      refine ⟨fun x ↦ ?_, fun V ↦ ?_⟩
      · obtain ⟨V, hVJ, y, hyV, hyx⟩ := Set.mem_iUnion₂.mp (hJcover (Set.mem_univ x))
        refine ⟨⟨V, hVJ⟩, ⟨y, hyV⟩, ?_⟩
        rw [hmap ⟨V, hVJ⟩]
        show ((BigFppfOver.toScheme B S hS).map pT).base y = x
        exact hyx
      · rw [hmap V]
        infer_instance
    have hOcover : Presieve.map (BigAffineFppf.toScheme B S hS) O.presieve₀ ∈
        Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T) :=
      Scheme.etalePrecoverage_le_fpqcPrecoverage _
        (by simpa [O, PreZeroHypercover.presieve₀_map] using hOcover_etale)
    choose E hEfinite hEcover hEfactor using fun V : J ↦ hf.2 (Wobj V.1) (jU V.1)
    have : Finite J := hJfinite.to_subtype
    have (V : J) : Finite (E V).I₀ := hEfinite V
    let W : PreZeroHypercover T :=
      { I₀ := Σ V : J, (E V).I₀
        X := fun ij ↦ (E ij.1).X ij.2
        f := fun ij ↦ (E ij.1).f ij.2 ≫ O.f ij.1 }
    refine ⟨W, inferInstance, ?_, fun ij ↦ ?_⟩
    · have hcomp := Precoverage.comp_mem_coverings (J := Scheme.fpqcPrecoverage)
        (X := fun V : J ↦ (BigAffineFppf.toScheme B S hS).obj (Wobj V.1))
        (f := fun V : J ↦ (BigAffineFppf.toScheme B S hS).map (jT V.1))
        (by simpa [O, PreZeroHypercover.presieve₀_map] using hOcover)
        (Y := fun (V : J) k ↦ (BigAffineFppf.toScheme B S hS).obj ((E V).X k))
        (g := fun (V : J) k ↦ (BigAffineFppf.toScheme B S hS).map ((E V).f k))
        (fun V ↦ by simpa [PreZeroHypercover.presieve₀_map] using hEcover V)
      simpa [W, O, PreZeroHypercover.presieve₀_map, Functor.map_comp] using hcomp
    · obtain ⟨i, b, hb⟩ := hEfactor ij.1 ij.2
      refine ⟨i, b ≫ pullback.snd a (f i).hom, ?_⟩
      have hj : jU ij.1.1 ≫ a =
          yoneda.map (jP ij.1.1 ≫ pT) ≫ h := by
        simp only [jU, Functor.map_comp, Category.assoc, ← hpb.w]
      calc
        (b ≫ pullback.snd a (f i).hom) ≫ (f i).hom =
            b ≫ pullback.fst a (f i).hom ≫ a := by
              rw [Category.assoc, pullback.condition]
        _ = yoneda.map ((BigAffineFppf.inclusion B S hS).map ((E ij.1).f ij.2)) ≫
            jU ij.1.1 ≫ a := by
              simpa [Category.assoc] using congrArg (fun q ↦ q ≫ a) hb
        _ = yoneda.map ((BigAffineFppf.inclusion B S hS).map ((E ij.1).f ij.2)) ≫
            yoneda.map (jP ij.1.1 ≫ pT) ≫ h := by rw [hj]
        _ = yoneda.map ((BigAffineFppf.inclusion B S hS).map (W.f ij)) ≫ h := by
              simp [W, O, jT, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
