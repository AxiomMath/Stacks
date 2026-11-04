module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms agreeing on the completion along a closed subset meeting every closed subset

Let `Y` be a locally Noetherian algebraic space over `S` and let `T ⊆ |Y|` be a closed subset
which meets every nonempty closed subset of `|Y|`. Two morphisms `a, b : Y ⟶ W` to an algebraic
space which induce the same morphism `Y_{/T} ⟶ W` on the completion along `T` are equal.

The typical instance is a space `Y` proper over `Spec R` for a ring `R` complete with respect to
an ideal `I`, with `T` the inverse image of `V(I)`: the image of a closed subset of `|Y|` is
closed in `Spec R`, and every nonempty closed subset of `Spec R` meets `V(I)` because `I` lies
in the Jacobson radical. This is the step of the existence half of [Stacks, Tag 0GI3] which
identifies the morphism `Spec Â ⟶ W` algebraizing the formal one with the given morphism off
`T`, without any agreement off `T` being assumed.

## Main results

* `AlgebraicGeometry.Space.eq_of_completion_eq_of_closed_meets`: the statement above.

## Implementation notes

The argument is the étale-local one of Stacks 0AR7/0GI1
(`AlgebraicGeometry.Space.comp_eq_of_sections`), run without the hypothesis off `T`. On a
locally Noetherian étale atlas `p : V ⟶ Y`, the locus `E ⟶ V` where `p ≫ a` and `p ≫ b` agree
is a monomorphism locally of finite type (Stacks 02X4), and it has sections over every
infinitesimal neighbourhood of the closed subscheme supported on the inverse image of `T`, so it
is étale at every point over `T` (Stacks 0A43). Hence every point of `T` lies in the image of an
étale morphism `q` from a representable presheaf with `q ≫ a = q ≫ b`. The union `G ⊆ |Y|` of
the images of all such `q` is open (Stacks 03IR) and contains `T`; its complement is a closed set
missing `T`, hence empty. Finally the base changes of the morphisms `q` to the atlas form an
fppf covering of `V` on whose members `p ≫ a` and `p ≫ b` agree.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Two morphisms agreeing on the completion along a closed subset which meets every
nonempty closed subset are equal.** Let `Y` be a locally Noetherian algebraic space over `S`,
`W` an algebraic space over `S`, and `T ⊆ |Y|` a closed subset meeting every nonempty closed
subset of `|Y|`. If `a, b : Y ⟶ W` induce the same morphism `Y_{/T} ⟶ W`, then `a = b`. -/
@[ega "I 10.9.4" "Necessity direction"]
theorem eq_of_completion_eq_of_closed_meets
    {Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hW : IsAlgebraicSpace B S hS W)
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS Y)} (hT : IsClosed T)
    (hmeets : ∀ C : Set (points B S hS Y), IsClosed C → C.Nonempty → (C ∩ T).Nonempty)
    (a b : Y ⟶ W)
    (hcompletion :
      (completionSubfunctor B S hS Y T).ι ≫ Functor.whiskerRight a uliftFunctor.{u + 1} =
        (completionSubfunctor B S hS Y T).ι ≫ Functor.whiskerRight b uliftFunctor.{u + 1}) :
    a = b := by
  obtain ⟨V, p, hsurj, hetale, hVnoeth⟩ := hYnoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVnoeth
  have hpEt : IsEtale B S hS p := isEtale_of_presheaf_etale B S hS hetale
  have hpsurj := surjective_pointsMap_of_presheaf_surjective B S hS p hsurj
  -- the inverse image of `T` in the atlas
  obtain ⟨Ws, hWsmem, hWsclosed⟩ :
      ∃ Ws : Set ((BigFppfOver.toScheme B S hS).obj V),
        (∀ w : points B S hS (yoneda.obj V),
          (pointsToScheme B S hS V w ∈ Ws ↔
            pointsMap B S hS (yoneda.obj V) p w ∈ T)) ∧ IsClosed Ws := by
    refine ⟨pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj V) p ⁻¹' T), ?_, ?_⟩
    · intro w
      refine ⟨?_, fun hw => ⟨w, hw, rfl⟩⟩
      rintro ⟨v, hv, hveq⟩
      exact injective_pointsToScheme B S hS V hveq ▸ hv
    · exact (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V _).mp
        (hT.preimage (continuous_pointsMap B S hS p))
  have hrange : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V)
      (w : points B S hS (yoneda.obj Zo)),
      pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj Zo) (yoneda.map z) w) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map z).base :=
    fun Zo z w => ⟨pointsToScheme B S hS Zo w, (pointsToScheme_pointsMap_yoneda B S hS z w).symm⟩
  -- agreement over every site object mapping into `Ws`
  have hin : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      Set.range ((BigFppfOver.toScheme B S hS).map z).base ⊆ Ws →
      yoneda.map z ≫ p ≫ a = yoneda.map z ≫ p ≫ b := by
    intro Zo z hz
    rw [← Category.assoc, ← Category.assoc]
    refine comp_eq_of_range_subset' B S hS a b hcompletion _ ?_
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact (hWsmem _).mp (hz (hrange Zo z w))
  -- the locus of the atlas where `p ≫ a` and `p ≫ b` agree
  have hmonoP := presheaf_monomorphisms_diag B S hS W hW
  have hlftP := presheaf_locallyOfFiniteType_diag B S hS W hW
  have hrep : yoneda.relativelyRepresentable (diag W) := hW.diagonal_representable
  let E := hrep.pullback (prod.lift (p ≫ a) (p ≫ b))
  let e : E ⟶ V := hrep.snd (prod.lift (p ≫ a) (p ≫ b))
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map e) := hmonoP.property_snd _
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map e) :=
    hlftP.property_snd _
  have hdict : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      yoneda.map z ≫ p ≫ a = yoneda.map z ≫ p ≫ b → ∃ w : Zo ⟶ E, w ≫ e = z := by
    intro Zo z hz
    have hi : (yoneda.map z ≫ p ≫ a) ≫ diag W =
        yoneda.map z ≫ prod.lift (p ≫ a) (p ≫ b) := by
      simp only [diag, prod.comp_lift, Category.comp_id, hz]
    exact ⟨hrep.lift (yoneda.map z ≫ p ≫ a) z hi, hrep.lift_snd _ _ _⟩
  have heq : yoneda.map e ≫ p ≫ a = yoneda.map e ≫ p ≫ b := by
    have hw := hrep.w (prod.lift (p ≫ a) (p ≫ b))
    have h4 := congrArg (fun α => α ≫ prod.fst) hw
    have h5 := congrArg (fun α => α ≫ prod.snd) hw
    simp only [diag, Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h4 h5
    exact h4.symm.trans h5
  -- a closed subscheme supported on `Ws`
  obtain ⟨Zs, i, hiCI, hirange⟩ :
      ∃ (Zs : Scheme.{u}) (i : Zs ⟶ (BigFppfOver.toScheme B S hS).obj V),
        AlgebraicGeometry.IsClosedImmersion i ∧ Set.range i.base = Ws :=
    ⟨_, (Scheme.IdealSheafData.vanishingIdeal (⟨Ws, hWsclosed⟩ :
      TopologicalSpace.Closeds ((BigFppfOver.toScheme B S hS).obj V))).subschemeι,
      inferInstance, by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl⟩
  have := hiCI
  -- the sections of the agreement locus over the infinitesimal neighbourhoods
  have hthick : ∀ n : ℕ, ∃ τ : Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n ⟶
      (BigFppfOver.toScheme B S hS).obj E,
      τ ≫ (BigFppfOver.toScheme B S hS).map e = Stacks.Thickenings.nthOrderToBase i n := by
    intro n
    have hmn : Mono (Stacks.Thickenings.nthOrderToBase i n) := by
      have heq' : Stacks.Thickenings.nthOrderToBase i n =
          (Scheme.Hom.ker (Scheme.Hom.liftCoborder i) ^ (n + 1)).subschemeι ≫
            (Scheme.Hom.coborderRange i).ι := rfl
      rw [heq']
      infer_instance
    let Zo : BigFppfOver B S hS := BigFppfOver.mk B S hS
      (B.contains_of_mono (Stacks.Thickenings.nthOrderToBase i n) V.left.2)
      (Stacks.Thickenings.nthOrderToBase i n ≫ B.inclusion.map V.hom)
    let z : Zo ⟶ V := Over.homMk (ObjectProperty.homMk (Stacks.Thickenings.nthOrderToBase i n))
      (by apply ObjectProperty.hom_ext; rfl)
    obtain ⟨w, hw⟩ := hdict Zo z
      (hin _ _ ((range_nthOrderToBase i n).trans_subset hirange.subset))
    exact ⟨(BigFppfOver.toScheme B S hS).map w,
      ((BigFppfOver.toScheme B S hS).map_comp w e).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map hw)⟩
  choose τ hτ using hthick
  -- (A) every point of `T` lies in the image of an étale chart on which `a` and `b` agree
  have hA : ∀ y ∈ T, ∃ (O : BigFppfOver B S hS) (q : yoneda.obj O ⟶ Y),
      IsEtale B S hS q ∧ y ∈ Set.range (pointsMap B S hS _ q) ∧ q ≫ a = q ≫ b := by
    intro y hy
    obtain ⟨w, hw⟩ := hpsurj y
    have hvWs : pointsToScheme B S hS V w ∈ Ws := (hWsmem w).mpr (hw ▸ hy)
    rw [← hirange] at hvWs
    obtain ⟨zz, hzz⟩ := hvWs
    set x := τ 0 (Stacks.Thickenings.nthOrderInclusion i 0 zz) with hx
    have hex : (BigFppfOver.toScheme B S hS).map e x = pointsToScheme B S hS V w := by
      have h0 : (BigFppfOver.toScheme B S hS).map e x =
          Stacks.Thickenings.nthOrderToBase i 0 (Stacks.Thickenings.nthOrderInclusion i 0 zz) := by
        rw [hx, ← hτ 0]
        rfl
      rw [h0, ← hzz]
      conv_rhs => rw [← Stacks.Thickenings.nthOrderInclusion_toBase i 0]
      rfl
    have hetx : EtaleAt ((BigFppfOver.toScheme B S hS).map e) x := by
      refine etaleAt_of_etale_infinitesimalNeighbourhoods _ i (fun n => ?_) x ?_
      · have := isIso_pullback_snd_of_section ((BigFppfOver.toScheme B S hS).map e)
          (Stacks.Thickenings.nthOrderToBase i n) (τ n) (hτ n)
        infer_instance
      · rw [hex, ← hzz]
        exact ⟨zz, rfl⟩
    obtain ⟨U, -, hxU, hUet⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt _ x hetx
    let O : BigFppfOver B S hS := BigFppfOver.mk B S hS (B.contains_of_mono U.ι E.left.2)
      (U.ι ≫ B.inclusion.map E.hom)
    let k : O ⟶ E := Over.homMk (ObjectProperty.homMk U.ι) (by apply ObjectProperty.hom_ext; rfl)
    have hk : (BigFppfOver.toScheme B S hS).map k = U.ι := rfl
    refine ⟨O, yoneda.map (k ≫ e) ≫ p, ?_, ?_, ?_⟩
    · refine isEtale_yoneda_map_comp B S hS p (k ≫ e) ?_ hpEt
      rw [Functor.map_comp, hk]
      exact hUet
    · obtain ⟨o, ho⟩ := surjective_pointsToScheme B S hS O ⟨x, hxU⟩
      refine ⟨o, ?_⟩
      rw [pointsMap_comp, Function.comp_apply, ← hw]
      congr 1
      apply injective_pointsToScheme B S hS V
      rw [pointsToScheme_pointsMap_yoneda, ho, ← hex, Functor.map_comp, hk]
      rfl
    · simp only [Functor.map_comp, Category.assoc]
      rw [heq]
  -- (B) the union of the images of such charts is open and contains `T`, hence is everything
  let G : Set (points B S hS Y) := {y | ∃ (O : BigFppfOver B S hS) (q : yoneda.obj O ⟶ Y),
      IsEtale B S hS q ∧ y ∈ Set.range (pointsMap B S hS _ q) ∧ q ≫ a = q ≫ b}
  have hGopen : IsOpen G := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨O, q, hq, hy, hab⟩
    exact ⟨_, fun y' hy' => ⟨O, q, hq, hy', hab⟩,
      isOpen_range_pointsMap_of_isEtale B S hS q (isAlgebraicSpace_yoneda B S hS O) hY hq, hy⟩
  have hGall : ∀ y, y ∈ G := by
    intro y₀
    by_contra hy₀
    obtain ⟨y, hyC, hyT⟩ := hmeets Gᶜ hGopen.isClosed_compl ⟨y₀, hy₀⟩
    exact hyC (hA y hyT)
  -- (C) the base changes of these charts cover the atlas
  have hC : ∀ v : (BigFppfOver.toScheme B S hS).obj V, ∃ (P : BigFppfOver B S hS) (pp : P ⟶ V),
      Etale ((BigFppfOver.toScheme B S hS).map pp) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map pp).base ∧
      yoneda.map pp ≫ p ≫ a = yoneda.map pp ≫ p ≫ b := by
    intro v
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS V v
    obtain ⟨O, q, hq, ⟨o, ho⟩, hab⟩ := hGall (pointsMap B S hS _ p w)
    obtain ⟨P, pp, qq, hpb, hppEt, -⟩ := exists_common_etale_chart B S hS ⟨Y, hY⟩ V O p q hpEt hq
    obtain ⟨wr, rfl⟩ := Quot.exists_rep w
    obtain ⟨orr, rfl⟩ := Quot.exists_rep o
    obtain ⟨r, hr, -⟩ := exists_fieldValuedPoint_of_isPullback B S hS pp qq p q hpb wr orr ho.symm
    refine ⟨P, pp, hppEt, ⟨pointsToScheme B S hS P (r.class B S hS _), ?_⟩, ?_⟩
    · rw [← pointsToScheme_pointsMap_yoneda, hr]
    · rw [← Category.assoc, hpb.w, Category.assoc, hab, ← Category.assoc, ← hpb.w,
        Category.assoc]
  choose P pp hppEt hppv hppab using hC
  have hcover := mem_topology_of_family B S hS (U := V)
    (I := ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj V)) (fun j => (P j.down).left)
    (fun j => (pp j.down).left)
    (fun j => by
      have := hppEt j.down
      exact inferInstanceAs (Flat ((BigFppfOver.toScheme B S hS).map (pp j.down))))
    (fun j => by
      have := hppEt j.down
      exact inferInstanceAs
        (LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (pp j.down))))
    (fun x => ⟨ULift.up x, hppv x⟩)
  have hsf : Presieve.IsSheafFor W (Presieve.ofArrows
      (fun j : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj V) =>
        (Over.mk ((pp j.down).left ≫ V.hom) : BigFppfOver B S hS))
      (fun j => (Over.homMk (pp j.down).left : Over.mk ((pp j.down).left ≫ V.hom) ⟶ V))) :=
    (Presieve.isSheafFor_iff_generate (P := W) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp hW.isSheaf) _ hcover)
  have hpab : p ≫ a = p ≫ b := by
    refine yonedaEquiv.injective (hsf.isSeparatedFor.ext fun R r hr => ?_)
    obtain ⟨j⟩ := hr
    have hiso : (Over.homMk (pp j.down).left : Over.mk ((pp j.down).left ≫ V.hom) ⟶ V) =
        (Over.isoMk (Iso.refl _) (by simp) :
          Over.mk ((pp j.down).left ≫ V.hom) ≅ P j.down).hom ≫ pp j.down := by
      ext
      simp
    have h := hppab j.down
    have h' : yoneda.map (Over.homMk (pp j.down).left :
        Over.mk ((pp j.down).left ≫ V.hom) ⟶ V) ≫ p ≫ a =
        yoneda.map (Over.homMk (pp j.down).left :
        Over.mk ((pp j.down).left ≫ V.hom) ⟶ V) ≫ p ≫ b := by
      rw [hiso, Functor.map_comp, Category.assoc, h, ← Category.assoc]
    simpa [yonedaEquiv_naturality] using congrArg yonedaEquiv h'
  exact hom_ext_of_etale_atlas B S hS hY.isSheaf hW.isSheaf p hsurj hetale hpab

end Space

end AlgebraicGeometry

end
