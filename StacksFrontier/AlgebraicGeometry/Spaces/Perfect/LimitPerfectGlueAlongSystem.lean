module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectBaseChangeEdsSystems
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackSquarePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SquareDerivedIsoLocality

/-!
# Glueing descended perfect objects across a morphism of elementary distinguished squares

Let `q : W_l ⟶ W_m` be covered by a morphism of elementary distinguished squares, from the square
`(U_l ⊆ W_l, V_l ⟶ W_l)` to the square `(U_m ⊆ W_m, V_m ⟶ W_m)`, and let the pieces `U_m`, `V_m`,
`P_m = U_m ×_{W_m} V_m` map compatibly to the pieces of a third square, over `W_i`.  In the
application `W_i`, `W_m` and `W_l` are two stages and the limit of a directed system, and the
squares are the base changes of one square.  Let `E` be an object of `D(𝒪_{W_l})`, and let `A` on
`U_i` and `Bo` on `V_i` be perfect objects whose derived pullbacks to `U_l` and `V_l` are the
restrictions of `E`.  Over `P_l` the restrictions of `A` and of `Bo` are then identified through
`E` (`AlgebraicGeometry.Space.DerivedPullbackComposition.limitComparisonIso`).  This file proves
that if that identification comes from an isomorphism `c` between the pullbacks to `P_m` of the
restrictions of `A` and of `Bo` to `P_i`, then `E` is the derived pullback along `q` of a perfect
object of `D(𝒪_{W_m})`.

This is the glueing in the step of the induction of Stacks 08GP for the essential surjectivity
half of Stacks 09RJ: the objects descended over `U` and over `V` are advanced to `W_m` and glued
there by Stacks 08HB (`AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_eds`), the glued
object being perfect because perfectness is local
(`AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`).  The compatibility over the
intersection that Stacks 08HB asks for is deduced from the prescription at `P_l` by pasting
square isomorphisms of derived pullback
(`AlgebraicGeometry.Space.DerivedPullbackComposition.map_squareIso_conj_eq_of_paste`).

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_iso_of_factorHom_eq_limitComparisonIso`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Glueing across a morphism of elementary distinguished squares -/

section Cube

variable {Wi Wm Wl : AlgebraicSpaces B S hS} {Vi Vm Vl : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Ui : Subfunctor Wi.1} {Um : Subfunctor Wm.1} {Ul : Subfunctor Wl.1}
  {fi : Vi ⟶ Wi.1} {fm : Vm ⟶ Wm.1} {fl : Vl ⟶ Wl.1}
  {hi : IsElementaryDistinguishedSquare B S hS Wi.2 Ui fi}
  {hm : IsElementaryDistinguishedSquare B S hS Wm.2 Um fm}
  {hl : IsElementaryDistinguishedSquare B S hS Wl.2 Ul fl}

/-- **Glueing descended perfect objects across a morphism of elementary distinguished squares.**
Let `q : W_l ⟶ W_m` be covered by a morphism of elementary distinguished squares (`rU`, `rV`,
`rP`), and let `tU`, `tV`, `tP` be compatible morphisms from the pieces of the square of `W_m` to
those of a square of `W_i`, with composites `qU`, `qV`, `qP`.  Let `A` on `U_i` and `Bo` on `V_i`
be perfect objects with `αU : Lq_U^*A ≅ E|_{U_l}` and `αV : Lq_V^*Bo ≅ E|_{V_l}`, and let `c` be an
isomorphism between the pullbacks along `tP` of the restrictions of `A` and of `Bo` to `P_i`
whose image under the map attached to `rP ≫ tP = qP` is the comparison
`AlgebraicGeometry.Space.DerivedPullbackComposition.limitComparisonIso` through `E`.  Then `E` is
the derived pullback along `q` of a perfect object of `D(𝒪_{W_m})`. -/
theorem exists_isPerfect_iso_of_factorHom_eq_limitComparisonIso (q : Wl ⟶ Wm)
    (rU : edsOpen B S hS hl ⟶ edsOpen B S hS hm) (rV : edsEtale B S hS hl ⟶ edsEtale B S hS hm)
    (rP : edsInter B S hS hl ⟶ edsInter B S hS hm)
    (hU : edsOpenHom B S hS hl ≫ q = rU ≫ edsOpenHom B S hS hm)
    (hV : edsEtaleHom B S hS hl ≫ q = rV ≫ edsEtaleHom B S hS hm)
    (hPU : edsFst B S hS hl ≫ rU = rP ≫ edsFst B S hS hm)
    (hPV : edsSnd B S hS hl ≫ rV = rP ≫ edsSnd B S hS hm)
    (tU : edsOpen B S hS hm ⟶ edsOpen B S hS hi) (tV : edsEtale B S hS hm ⟶ edsEtale B S hS hi)
    (tP : edsInter B S hS hm ⟶ edsInter B S hS hi)
    (h₂ : edsFst B S hS hm ≫ tU = tP ≫ edsFst B S hS hi)
    (k₂ : edsSnd B S hS hm ≫ tV = tP ≫ edsSnd B S hS hi)
    (qU : edsOpen B S hS hl ⟶ edsOpen B S hS hi) (qV : edsEtale B S hS hl ⟶ edsEtale B S hS hi)
    (qP : edsInter B S hS hl ⟶ edsInter B S hS hi)
    (hqU : rU ≫ tU = qU) (hqV : rV ≫ tV = qV) (hqP : rP ≫ tP = qP)
    (h₃ : edsFst B S hS hl ≫ qU = qP ≫ edsFst B S hS hi)
    (k₃ : edsSnd B S hS hl ≫ qV = qP ≫ edsSnd B S hS hi)
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Wl))
      _ _ (HasDerivedCategory.standard _))
    (A : @DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hi)))
        _ _ (HasDerivedCategory.standard _))
    (Bo : @DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hi)))
        _ _ (HasDerivedCategory.standard _))
    (hA : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (edsOpen B S hS hi).1 (edsOpen B S hS hi).2)
      (smallEtaleRingedSite B S hS (edsOpen B S hS hi).1 (edsOpen B S hS hi).2).IsPerfect A)
    (hBo : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (edsEtale B S hS hi).1
      (edsEtale B S hS hi).2)
      (smallEtaleRingedSite B S hS (edsEtale B S hS hi).1
      (edsEtale B S hS hi).2).IsPerfect Bo)
    (αU : (smallEtaleDerivedModulePullback B S hS qU).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hl)).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS qV).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hl)).obj E)
    (c : (smallEtaleDerivedModulePullback B S hS tP).obj
        ((smallEtaleDerivedModulePullback B S hS (edsFst B S hS hi)).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS tP).obj
        ((smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hi)).obj Bo))
    (hc : (DerivedPullbackComposition.canonical B S hS).factorHom rP tP qP hqP _ _ c.hom =
      ((DerivedPullbackComposition.canonical B S hS).limitComparisonIso (edsFst B S hS hl) qU qP
        (edsFst B S hS hi) h₃ (edsSnd B S hS hl) qV (edsSnd B S hS hi) k₃ (edsOpenHom B S hS hl)
        (edsEtaleHom B S hS hl) (isPullback_edsInter B S hS hl).flip.w A Bo E αU αV).hom) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Wm.1 Wm.2)
    ∃ F : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Wm))
      _ _ (HasDerivedCategory.standard _),
      (smallEtaleRingedSite B S hS Wm.1 Wm.2).IsPerfect F ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS q).obj F ≅ E) := by
  let := fun (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) =>
    HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  have hc' := (DerivedPullbackComposition.canonical B S hS).map_squareIso_conj_eq_of_paste
    rP tP qP hqP rU tU qU hqU rV tV qV hqV
    (edsFst B S hS hl) (edsFst B S hS hm) (edsFst B S hS hi) hPU h₂ h₃
    (edsSnd B S hS hl) (edsSnd B S hS hm) (edsSnd B S hS hi) hPV k₂ k₃
    (edsOpenHom B S hS hl) (edsEtaleHom B S hS hl) (isPullback_edsInter B S hS hl).flip.w
    A Bo E αU αV (((DerivedPullbackComposition.canonical B S hS).iso rU tU qU hqU).app A ≪≫ αU)
    (Iso.trans_hom _ _)
    (((DerivedPullbackComposition.canonical B S hS).iso rV tV qV hqV).app Bo ≪≫ αV)
    (Iso.trans_hom _ _) c hc
    ((((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hm) tU tP
        (edsFst B S hS hi) h₂).app A).symm ≪≫ c ≪≫
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hm) tV tP
        (edsSnd B S hS hi) k₂).app Bo)
    (by rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom])
  obtain ⟨F, f, g, ⟨e⟩⟩ := exists_glue_derivedPullback_iso_of_eds hm hl q rU rV rP hU hV hPU hPV E
    ((smallEtaleDerivedModulePullback B S hS tU).obj A)
    ((smallEtaleDerivedModulePullback B S hS tV).obj Bo) _ _ _ hc'
  refine ⟨F, isPerfect_of_isPerfect_edsRestrict B S hS hm F
    ((isPerfect_smallEtaleDerivedModulePullback_obj_iff B S hS _
      (isEtale_edsOpenHom B S hS hm) F).1
      (RingedSite.IsPerfect.of_iso _ (isPerfect_smallEtaleDerivedModulePullback tU A hA) f.symm))
    ((isPerfect_smallEtaleDerivedModulePullback_obj_iff B S hS _
      (isEtale_edsEtaleHom B S hS hm) F).1
      (RingedSite.IsPerfect.of_iso _ (isPerfect_smallEtaleDerivedModulePullback tV Bo hBo)
        g.symm)), ⟨e⟩⟩

end Cube

end AlgebraicGeometry.Space

end
