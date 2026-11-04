module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SheafCoproduct

/-!
# Coproduct decompositions of representable fppf sheaves

If the sheaf represented by a scheme is a coproduct of sheaves, each summand is represented
by an open and closed subscheme, and those subschemes form a coproduct decomposition of the
original scheme.

## Main results

* `AlgebraicGeometry.Space.exists_clopen_scheme_coproduct` constructs the open-and-closed
  representing subschemes and their coproduct decomposition.

## Implementation notes

The sheaf coproduct is supplied as a colimit cocone, and representability of its vertex is
an isomorphism of presheaves with a Yoneda presheaf. The representing isomorphisms for the
summands commute with the coproduct inclusions, so they identify the specified decomposition
rather than merely unrelated representatives. The resulting coproduct is asserted in schemes.

Each summand is cut out as the first leg of a binary coproduct, by
`AlgebraicGeometry.Space.splitColimit`, so
`AlgebraicGeometry.coproductInl_isOpenImmersion` applies to it. That the representing
subschemes decompose the ambient scheme is checked after Yoneda: the representable presheaf
of a scheme on the big fppf site is computed by the continuous functor to schemes, so a
cofan of schemes is a colimit as soon as the corresponding cofan of sheaves is.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- Alias of `AlgebraicGeometry.BigFppfSite.inclusion_isContinuous`. -/
alias bigFppf_inclusion_isContinuous := AlgebraicGeometry.BigFppfSite.inclusion_isContinuous

/-- A sheaf coproduct represented by a scheme comes from an open-and-closed
coproduct decomposition of that scheme. -/
@[stacks 02WO]
theorem exists_clopen_scheme_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F)
    (hcoprod : IsColimit (Cofan.mk F ι))
    (U : BigFppfOver B S hS)
    (e : F.obj ≅ yoneda.obj U) :
    ∃ (Uᵢ : I → BigFppfOver B S hS)
      (j : ∀ i, Uᵢ i ⟶ U)
      (eᵢ : ∀ i, (Fᵢ i).obj ≅ yoneda.obj (Uᵢ i)),
      (∀ i, AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      (∀ i, AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      (∀ i, (eᵢ i).hom ≫ yoneda.map (j i) = (ι i).hom ≫ e.hom) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj U)
        (fun i => (BigFppfOver.toScheme B S hS).map (j i)))) := by
  classical
  let J := BigFppfOver.topology B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let T := BigFppfOver.toScheme B S hS
  let G : I → Sheaf J (Type u) := fun i => otherSheaf (J := J) (fun k => (ι k).hom) i
  let g : ∀ i, G i ⟶ F := fun i => otherInclusion (J := J) (fun k => (ι k).hom) i
  have hbin : ∀ i, IsColimit (BinaryCofan.mk (ι i) (g i)) := fun i => splitColimit ι hcoprod i
  let hopen : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T)) (ι i).hom :=
    fun i => _root_.AlgebraicGeometry.coproductInl_isOpenImmersion B S hS (Fᵢ i) (G i) F
      (ι i) (g i) (hbin i)
  have hclosed : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) T))
        (ι i).hom :=
    fun i => _root_.AlgebraicGeometry.coproductInl_isClosedImmersion B S hS (Fᵢ i) (G i) F
      (ι i) (g i) (hbin i)
  let Ui : I → BigFppfOver B S hS := fun i => (hopen i).rep.pullback e.inv
  let j : ∀ i, Ui i ⟶ U := fun i => (hopen i).rep.snd e.inv
  let f : ∀ i, yoneda.obj (Ui i) ⟶ (Fᵢ i).obj := fun i => (hopen i).rep.fst e.inv
  have hpb := fun i => (hopen i).rep.isPullback e.inv
  have hiso : ∀ i, IsIso (f i) := fun i => (hpb i).isIso_fst_of_isIso
  let eᵢ : ∀ i, (Fᵢ i).obj ≅ yoneda.obj (Ui i) := fun i => (asIso (f i)).symm
  have hcompat : ∀ i, (eᵢ i).hom ≫ yoneda.map (j i) = (ι i).hom ≫ e.hom := by
    intro i
    have hfac : f i ≫ (ι i).hom ≫ e.hom = yoneda.map (j i) := by
      simpa using congrArg (fun q => q ≫ e.hom) (hpb i).w
    simp [eᵢ, ← hfac]
  let ff := fullyFaithfulSheafToPresheaf J (Type u)
  let eS : F ≅ J.yoneda.obj U := ff.preimageIso e
  let eᵢS : ∀ i, Fᵢ i ≅ J.yoneda.obj (Ui i) := fun i => ff.preimageIso (eᵢ i)
  have hcompatS : ∀ i, (eᵢS i).hom ≫ J.yoneda.map (j i) = ι i ≫ eS.hom := by
    intro i
    apply (sheafToPresheaf J (Type u)).map_injective
    simpa [eS, eᵢS, ff, Functor.map_comp] using hcompat i
  let cY : Cofan (fun i => J.yoneda.obj (Ui i)) :=
    Cofan.mk (J.yoneda.obj U) (fun i => J.yoneda.map (j i))
  have hcomm (i : I) : J.yoneda.map (j i) ≫ eS.inv = (eᵢS i).inv ≫ (ι i) := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hcompatS i, Iso.inv_hom_id_assoc]
  have hY : IsColimit cY := by
    let d (t : Cofan (fun i => J.yoneda.obj (Ui i))) : F ⟶ t.pt :=
      hcoprod.desc (Cofan.mk t.pt (fun i => (eᵢS i).hom ≫ t.inj i))
    have hd (t : Cofan (fun i => J.yoneda.obj (Ui i))) (i : I) :
        ι i ≫ d t = (eᵢS i).hom ≫ t.inj i := hcoprod.fac _ ⟨i⟩
    refine Cofan.IsColimit.mk cY (fun t => eS.inv ≫ d t) ?_ ?_
    · intro t i
      change (J.yoneda.map (j i) ≫ eS.inv) ≫ d t = _
      rw [hcomm i, Category.assoc, hd, Iso.inv_hom_id_assoc]
    · intro t m hm
      have hq : eS.hom ≫ m = d t := by
        apply hcoprod.hom_ext
        rintro ⟨i⟩
        change ι i ≫ eS.hom ≫ m = ι i ≫ d t
        rw [hd, ← hm i, ← Category.assoc, ← Category.assoc, ← hcompatS i]
        rfl
      exact (Iso.eq_inv_comp eS).2 hq
  have _ : B.inclusion.IsContinuous B.topology Scheme.fppfTopology :=
    bigFppf_inclusion_isContinuous B
  have _ : T.IsContinuous J Scheme.fppfTopology := by
    dsimp [T, BigFppfOver.toScheme, BigFppfOver.forget]
    exact Functor.isContinuous_comp (Over.forget (B.obj hS)) B.inclusion J
      B.topology Scheme.fppfTopology
  let HX (X : Scheme.{u}) : Sheaf J (Type u) :=
    ⟨T.op ⋙ yoneda.obj X,
      (isSheaf_iff_isSheaf_of_type J _).2
        (T.op_comp_isSheaf_of_types J Scheme.fppfTopology
        ⟨yoneda.obj X,
            (isSheaf_iff_isSheaf_of_type Scheme.fppfTopology _).2
                (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
                  (J := Scheme.fppfTopology) (yoneda.obj X))⟩)⟩
  have hHX_map (X : Scheme.{u}) {V W : BigFppfOver B S hS}
      (g : V ⟶ W) (f : T.obj W ⟶ X) :
      (HX X).obj.map g.op f = T.map g ≫ f := rfl
  let γ {V : BigFppfOver B S hS} {X : Scheme.{u}}
      (f : T.obj V ⟶ X) : J.yoneda.obj V ⟶ HX X := J.yonedaEquiv.symm f
  let cScheme : Cofan (fun i => T.obj (Ui i)) :=
    Cofan.mk (T.obj U) (fun i => T.map (j i))
  let desc (t : Cofan (fun i => T.obj (Ui i))) : T.obj U ⟶ t.pt :=
    J.yonedaEquiv (Cofan.IsColimit.desc hY (fun i => γ (t.inj i)))
  have hγ (t : Cofan (fun i => T.obj (Ui i))) (i : I) :
      J.yonedaEquiv (γ (t.inj i)) = t.inj i := by simp [γ]
  have hScheme : IsColimit cScheme := by
    refine Cofan.IsColimit.mk cScheme desc ?_ ?_
    · intro t i
      have hfac := Cofan.IsColimit.fac hY (fun k => γ (t.inj k)) i
      change J.yoneda.map (j i) ≫
        Cofan.IsColimit.desc hY (fun k => γ (t.inj k)) = γ (t.inj i) at hfac
      have hfac' := congrArg J.yonedaEquiv hfac
      rw [← J.yonedaEquiv_naturality
        (Cofan.IsColimit.desc hY (fun k => γ (t.inj k))) (j i), hγ t i,
        hHX_map t.pt (j i) _] at hfac'
      show T.map (j i) ≫ desc t = t.inj i
      simpa [HX, desc] using hfac'
    · intro t m hm
      let mSheaf : J.yoneda.obj U ⟶ HX t.pt := γ m
      have hleg (i : I) : J.yoneda.map (j i) ≫ mSheaf = γ (t.inj i) := by
        apply J.yonedaEquiv.injective
        calc
          J.yonedaEquiv (J.yoneda.map (j i) ≫ mSheaf) =
              (HX t.pt).obj.map (j i).op (J.yonedaEquiv mSheaf) :=
            (J.yonedaEquiv_naturality mSheaf (j i)).symm
          _ = T.map (j i) ≫ m := by
            simpa [mSheaf, γ] using hHX_map t.pt (j i) m
          _ = t.inj i := hm i
          _ = J.yonedaEquiv (γ (t.inj i)) := (hγ t i).symm
      have heq : Cofan.IsColimit.desc hY (fun i => γ (t.inj i)) = mSheaf :=
        hY.hom_ext fun ⟨i⟩ => (Cofan.IsColimit.fac hY (fun k => γ (t.inj k)) i).trans (hleg i).symm
      exact (congrArg J.yonedaEquiv heq).symm
  exact ⟨Ui, j, eᵢ,
    fun i => (hopen i).property e.inv (f i) (j i) (hpb i),
    fun i => (hclosed i).property e.inv (f i) (j i) (hpb i),
    hcompat, ⟨hScheme⟩⟩

end AlgebraicGeometry.Space

end
