module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilDivisorAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackIsomorphism

/-!
# Axiom (A1) for de Rham cohomology

Axiom (A1) of Weil Cohomology Theories, Section 0FID asks that `H^*` be compatible with finite
coproducts: `H^*(∅) = 0`, and for a coproduct `X ⨿ Y` with coprojections `i`, `j` the map
`(i^*, j^*) : H^*(X ⨿ Y) ⟶ H^*(X) × H^*(Y)` is bijective. For de Rham cohomology over a field this
holds because de Rham cohomology is the cohomology of a complex of sheaves (Section 0FWC): along a
decomposition of a scheme into finitely many open and closed pieces it splits as the product of
the de Rham cohomology of the pieces (`Stacks.DeRhamClopen.bijective_deRhamPullbackSquare`).

## Main results

* `Stacks.DeRhamWeil.bijective_pullbackPiece_prod`: `(i^*, j^*)` is bijective in every degree.
* `Stacks.DeRhamWeil.coproductAxiom`: **axiom (A1)** for the data
  `Stacks.DeRhamWeil.deRhamFirstChernClassData`.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamBaseChange

universe u

namespace Stacks.DeRhamWeil

variable {k : Type u} [Field k]

/-- `H^*_{dR}(∅/k) = 0`: an empty scheme is the union of no open and closed pieces. -/
theorem subsingleton_piece_of_isEmpty (X : (SmoothProjectiveScheme k).FullSubcategory)
    (hX : IsEmpty ((toScheme k).obj X)) (n : ℤ) : Subsingleton (piece X n) := by
  have hcov : (⨆ i : Empty, (Empty.elim i : ((toScheme k).obj X).Opens)) = ⊤ := by
    ext x
    exact hX.elim x
  exact ⟨fun a b => (Stacks.DeRhamClopen.bijective_deRhamPullbackSquare X.obj.hom
    (fun i : Empty => Empty.elim i) (fun i => i.elim) (fun i => i.elim) hcov n).1
    (funext fun i => i.elim)⟩

/-- The coprojections of a binary coproduct of schemes are open immersions. -/
private theorem isOpenImmersion_of_isColimit_binaryCofan {A B C : Scheme.{u}} {f : A ⟶ C}
    {g : B ⟶ C} (hc : IsColimit (BinaryCofan.mk f g)) : IsOpenImmersion f ∧ IsOpenImmersion g := by
  let e := hc.coconePointUniqueUpToIso (coprodIsCoprod A B)
  have hf : coprod.inl ≫ e.inv = f :=
    hc.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod _ _) ⟨WalkingPair.left⟩
  have hg : coprod.inr ≫ e.inv = g :=
    hc.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod _ _) ⟨WalkingPair.right⟩
  have hinl : IsOpenImmersion (coprod.inl : A ⟶ A ⨿ B) := inferInstance
  have hinr : IsOpenImmersion (coprod.inr : B ⟶ A ⨿ B) := inferInstance
  rw [← hf, ← hg]
  exact ⟨@IsOpenImmersion.comp _ _ _ _ e.inv hinl inferInstance,
    @IsOpenImmersion.comp _ _ _ _ e.inv hinr inferInstance⟩

/-- The images of the coprojections of a binary coproduct of schemes are complementary clopen
subsets. -/
private theorem isCompl_opensRange_of_isColimit_binaryCofan {A B C : Scheme.{u}} {f : A ⟶ C}
    {g : B ⟶ C} [IsOpenImmersion f] [IsOpenImmersion g] (hc : IsColimit (BinaryCofan.mk f g)) :
    IsCompl f.opensRange g.opensRange ∧ IsClopen (f.opensRange : Set C) ∧
      IsClopen (g.opensRange : Set C) := by
  have htop := (TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ hc⟩
  have hrange : IsCompl (Set.range f.base) (Set.range g.base) := htop.2.2
  refine ⟨?_, ⟨?_, f.opensRange.isOpen⟩, ⟨?_, g.opensRange.isOpen⟩⟩
  · simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj,
      Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_sup,
      TopologicalSpace.Opens.coe_bot, TopologicalSpace.Opens.coe_top]
    exact ⟨disjoint_iff.mp hrange.disjoint, codisjoint_iff.mp hrange.codisjoint⟩
  · rw [Scheme.Hom.coe_opensRange, ← hrange.symm.compl_eq]
    exact htop.2.1.isOpen_range.isClosed_compl
  · rw [Scheme.Hom.coe_opensRange, ← hrange.compl_eq]
    exact htop.1.isOpen_range.isClosed_compl

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- The square exhibiting `X ≅ f(X)` over `Spec k` for an open immersion `f : X ⟶ Z`. -/
private theorem isoOpensRange_square_w (f : X ⟶ Z) [IsOpenImmersion ((toScheme k).map f)] :
    ((toScheme k).map f).isoOpensRange.hom ≫ ((toScheme k).map f).opensRange.ι ≫ Z.obj.hom =
      X.obj.hom ≫ 𝟙 _ := by
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  exact square_w f

/-- For an open immersion `f : X ⟶ Z`, `f^*` on `H^n_{dR}` is the restriction to the image of `f`
followed by the pullback along the isomorphism `X ≅ f(X)`. -/
private theorem pullbackPiece_eq_isoOpensRange (f : X ⟶ Z) [IsOpenImmersion ((toScheme k).map f)]
    (n : ℤ) (z : piece Z n) :
    pullbackPiece f n z = deRhamPullbackSquare ((toScheme k).map f).isoOpensRange.hom X.obj.hom
      (((toScheme k).map f).opensRange.ι ≫ Z.obj.hom) (𝟙 _) (isoOpensRange_square_w f) n
      (deRhamPullbackSquare ((toScheme k).map f).opensRange.ι
        (((toScheme k).map f).opensRange.ι ≫ Z.obj.hom) Z.obj.hom (𝟙 _)
        (Category.comp_id _).symm n z) :=
  ((deRhamPullbackSquare_comp ((toScheme k).map f).opensRange.ι
      (((toScheme k).map f).opensRange.ι ≫ Z.obj.hom) Z.obj.hom (𝟙 _) (Category.comp_id _).symm
      ((toScheme k).map f).isoOpensRange.hom X.obj.hom (𝟙 _) (isoOpensRange_square_w f)
      (by rw [Category.assoc, isoOpensRange_square_w]; simp) n z).trans
    (deRhamPullbackSquare_congr X.obj.hom Z.obj.hom
      (Scheme.Hom.isoOpensRange_hom_ι ((toScheme k).map f))
      (Category.comp_id _) _ (square_w f) n z)).symm

/-- **`(i^*, j^*) : H^n_{dR}(Z/k) ⟶ H^n_{dR}(X/k) × H^n_{dR}(Y/k)` is bijective** for a coproduct
`Z = X ⨿ Y` of smooth projective `k`-schemes with coprojections `i` and `j`. -/
theorem bijective_pullbackPiece_prod (i : X ⟶ Z) (j : Y ⟶ Z)
    (hc : IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map j))) (n : ℤ) :
    Function.Bijective (fun z : piece Z n => (pullbackPiece i n z, pullbackPiece j n z)) := by
  obtain ⟨_, _⟩ := isOpenImmersion_of_isColimit_binaryCofan hc
  obtain ⟨hcompl, hi, hj⟩ := isCompl_opensRange_of_isColimit_binaryCofan hc
  let U : Bool → ((toScheme k).obj Z).Opens :=
    fun b => cond b ((toScheme k).map i).opensRange ((toScheme k).map j).opensRange
  have hdisj : ∀ a b, a ≠ b → Disjoint (U a) (U b) := by
    rintro (_ | _) (_ | _) hab
    · exact absurd rfl hab
    · exact hcompl.disjoint.symm
    · exact hcompl.disjoint
    · exact absurd rfl hab
  have hsplit := Stacks.DeRhamClopen.bijective_deRhamPullbackSquare Z.obj.hom U
    (fun b => by cases b; exacts [hj, hi]) hdisj
    (by rw [iSup_bool_eq]; exact hcompl.sup_eq_top) n
  have hPi := bijective_deRhamPullbackSquare_of_isIso _ _ _ (isoOpensRange_square_w i) n
  have hPj := bijective_deRhamPullbackSquare_of_isIso _ _ _ (isoOpensRange_square_w j) n
  refine ⟨fun z z' hzz => ?_, fun ab => ?_⟩
  · simp only [Prod.mk.injEq, pullbackPiece_eq_isoOpensRange] at hzz
    refine hsplit.1 (funext fun b => ?_)
    cases b
    · exact hPj.1 hzz.2
    · exact hPi.1 hzz.1
  · obtain ⟨a0, ha0⟩ := hPi.2 ab.1
    obtain ⟨b0, hb0⟩ := hPj.2 ab.2
    obtain ⟨z, hz⟩ := hsplit.2 (fun b => Bool.rec (motive := fun b =>
      AlgebraicGeometry.SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras ((U b).ι ≫ Z.obj.hom))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras ((U b).ι ≫ Z.obj.hom))) n) b0 a0 b)
    refine ⟨z, Prod.ext ?_ ?_⟩
    · show pullbackPiece i n z = ab.1
      rw [pullbackPiece_eq_isoOpensRange, ← ha0]
      exact congrArg _ (congrFun hz true)
    · show pullbackPiece j n z = ab.2
      rw [pullbackPiece_eq_isoOpensRange, ← hb0]
      exact congrArg _ (congrFun hz false)

/-- **`(i^*, j^*) : H^*_{dR}(Z/k) ⟶ H^*_{dR}(X/k) × H^*_{dR}(Y/k)` is bijective** for a coproduct
`Z = X ⨿ Y` of smooth projective `k`-schemes. -/
theorem bijective_pullback_prod (i : X ⟶ Z) (j : Y ⟶ Z)
    (hc : IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map j))) :
    Function.Bijective (fun a : cohomology Z => (pullback i a, pullback j a)) := by
  classical
  let Φ := fun n => Equiv.ofBijective _ (bijective_pullbackPiece_prod i j hc n)
  refine ⟨fun a b hab => ?_, fun xy => ?_⟩
  · simp only [Prod.mk.injEq] at hab
    ext n
    apply (Φ n).injective
    show (pullbackPiece i n (a n), pullbackPiece j n (a n)) =
      (pullbackPiece i n (b n), pullbackPiece j n (b n))
    rw [← pullback_apply_component, ← pullback_apply_component, ← pullback_apply_component,
      ← pullback_apply_component, hab.1, hab.2]
  · let z : cohomology Z := DFinsupp.mk (xy.1.support ∪ xy.2.support)
      (fun n => (Φ n.1).symm (xy.1 n.1, xy.2 n.1))
    have hz : ∀ n, (pullbackPiece i n (z n), pullbackPiece j n (z n)) = (xy.1 n, xy.2 n) := by
      intro n
      by_cases hn : n ∈ xy.1.support ∪ xy.2.support
      · rw [show z n = (Φ n).symm (xy.1 n, xy.2 n) from DFinsupp.mk_of_mem hn]
        exact (Φ n).apply_symm_apply _
      · rw [show z n = 0 from DFinsupp.mk_of_notMem hn, map_zero, map_zero]
        simp only [Finset.mem_union, DFinsupp.mem_support_toFun, ne_eq, not_or, not_not] at hn
        rw [hn.1, hn.2]
    refine ⟨z, Prod.ext ?_ ?_⟩ <;> ext n <;> rw [pullback_apply_component]
    exacts [congrArg Prod.fst (hz n), congrArg Prod.snd (hz n)]

/-- **Axiom (A1) for de Rham cohomology**: `H^*_{dR}` is compatible with finite coproducts,
`H^*_{dR}(∅/k) = 0` and `(i^*, j^*) : H^*_{dR}(X ⨿ Y/k) ≅ H^*_{dR}(X/k) × H^*_{dR}(Y/k)`
(Section 0FWC: de Rham cohomology is the cohomology of a complex of sheaves). -/
theorem coproductAxiom : (deRhamFirstChernClassData k).CoproductAxiom :=
  ⟨fun X hX => ⟨fun _ _ => DFinsupp.ext fun n => (subsingleton_piece_of_isEmpty X hX n).elim _ _⟩,
    fun _ _ _ i j ⟨hc⟩ => bijective_pullback_prod i j hc⟩

end Stacks.DeRhamWeil

end
