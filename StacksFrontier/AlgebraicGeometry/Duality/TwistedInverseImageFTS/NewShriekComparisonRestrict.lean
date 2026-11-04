module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualityRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparison
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# `f^! ≅ f_new^!` restricted to an open

Let `g : X ⟶ Y` be a separated morphism of schemes of finite type over a Noetherian base, `j` a
compactification of `g`, `K` a dualizing complex on `Y` and `e : g^!K ≅ ω`. The isomorphism
`g^! M ≅ R𝓗om(Lg^* D_Y(M), ω) = g_new^! M` of [Stacks, Tag 0AUE] restricts along an open
immersion `h : X' ⟶ X` to the one for `h ≫ g`, at the compactification `X' ⊆ X ⊆ X̄` and the
identification `(h ≫ g)^!K ≅ Lh^*(g^!K) ≅ Lh^*ω`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekOfIso_hom_app`: the components.
* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekOfIso_restrict`: the restriction.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.NormalizedOnOpens

open Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

section
variable {T : Scheme.{u}} [AlgebraicGeometry.IsNoetherian T] {A B : FTS T} (g : A ⟶ B)
  (j : CompactificationOf (Over.mk g.left)) {K : Std B.left} (hK : IsDualizing K) {ω : Std A.left}
  (e : upperShriekDualizing g j hK ≅ ω)

/-- The components of `upperShriekStdIsoFNewShriekOfIso`. -/
theorem upperShriekStdIsoFNewShriekOfIso_hom_app (M : (plusCoh B.left).FullSubcategory) :
    (upperShriekStdIsoFNewShriekOfIso g j hK e).hom.app M =
      (upperShriekDualityIso g j hK).hom.app M ≫
        ((sheafHom A.left).obj ((pull g.left).op.obj
          (((sheafHom B.left).flip.obj K).rightOp.obj ((plusCoh B.left).ι.obj M)))).map e.hom ≫
        (relativeDualIsoSheafHom ω).inv.app ((pull g.left).op.obj
          (((sheafHom B.left).flip.obj K).rightOp.obj ((plusCoh B.left).ι.obj M))) ≫
        ((pull g.left).op ⋙ dualInto ω).map
          ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app
            ((plusCoh B.left).ι.obj M)) := by
  simp only [upperShriekStdIsoFNewShriekOfIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.mapIso_hom, Functor.flip_map_app,
    Category.assoc]
end

section
variable {V X : Scheme.{u}} (ι : V ⟶ X) [IsOpenImmersion ι]

/-- The components of `pullDualIso`, with the identifications `relativeDualIsoSheafHom` kept. -/
theorem _root_.Stacks.Duality.pullDualIso_hom_app_eq (ωX : Std X) (P : (Std X)ᵒᵖ) :
    (pullDualIso ι ωX).hom.app P =
      (pull ι).map ((relativeDualIsoSheafHom ωX).hom.app P) ≫ pullSheafHomMap ι P.unop ωX ≫
        (relativeDualIsoSheafHom ((pull ι).obj ωX)).inv.app ((pull ι).op.obj P) := by
  simp only [pullDualIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    UpperShriekDuality.pullSheafHomIso_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom]
end

/-- The chase behind `upperShriekStdIsoFNewShriekOfIso_restrict`. -/
theorem upperShriekStdIsoFNewShriekOfIso_restrict_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (L : 𝒟 ⥤ 𝒞) {a0 a1 a2 a3 a4 b2 : 𝒟} {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : 𝒞}
    (u : a0 ⟶ a1) (se : a1 ⟶ a2) (ri : a2 ⟶ a3) (fν : a3 ⟶ a4) (sfν : a2 ⟶ b2) (rid : b2 ⟶ a4)
    (rh : a4 ⟶ b2) (psmd : L.obj b2 ⟶ c1) (rLi : c1 ⟶ c2) (dpc : c2 ⟶ c3)
    (psms : L.obj a2 ⟶ c4) (sLl : c4 ⟶ c1) (sx : c1 ⟶ c5) (rLid : c5 ⟶ c3)
    (spciω : c4 ⟶ c6) (sν' : c6 ⟶ c5) (psmD : L.obj a1 ⟶ c7) (sLe0 : c7 ⟶ c4)
    (spciD : c7 ⟶ c8) (sLe : c8 ⟶ c6) (sd : c8 ⟶ c9) (se' : c9 ⟶ c6) (r1 : L.obj a0 ⟶ c10)
    (u' : c10 ⟶ c9) (rLi' : c6 ⟶ c11) (fν' : c11 ⟶ c3) {O : a0 ⟶ a4} {fN : L.obj a4 ⟶ c3}
    {pdi : L.obj a4 ⟶ c2} {O' : c10 ⟶ c3}
    (F1 : sfν ≫ rid = ri ≫ fν) (F2 : rid ≫ rh = 𝟙 _) (F3 : L.map sfν ≫ psmd = psms ≫ sLl)
    (F8 : rLi ≫ dpc = sx ≫ rLid) (F10 : sLl ≫ sx = spciω ≫ sν')
    (F7 : L.map se ≫ psms = psmD ≫ sLe0) (F6 : spciD ≫ sLe = sLe0 ≫ spciω) (F5 : sd ≫ se' = sLe)
    (T2 : L.map u ≫ psmD ≫ spciD ≫ sd = r1 ≫ u') (F9 : rLi' ≫ fν' = sν' ≫ rLid)
    (hO : O = u ≫ se ≫ ri ≫ fν) (hN : fN = pdi ≫ dpc) (hP : pdi = L.map rh ≫ psmd ≫ rLi)
    (hO' : O' = u' ≫ se' ≫ rLi' ≫ fν') :
    L.map O ≫ fN = r1 ≫ O' := by
  subst hO hN hP hO'
  have F12 : L.map ri ≫ L.map fν ≫ L.map rh = L.map sfν := by
    rw [← L.map_comp, ← L.map_comp, ← reassoc_of% F1, F2, Category.comp_id]
  simp only [L.map_comp, Category.assoc]
  rw [reassoc_of% F12, reassoc_of% F3, F8, reassoc_of% F10, reassoc_of% F7, ← reassoc_of% F6,
    ← reassoc_of% F5, reassoc_of% T2, F9]

/-- `G.map δ.hom ≫ G.map (δ.symm ≪≫ ε).hom = G.map ε.hom`. -/
theorem map_hom_comp_map_symm_trans_hom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {a b c : 𝒞} (δ : a ≅ b) (ε : a ≅ c) : G.map δ.hom ≫ G.map (δ.symm ≪≫ ε).hom = G.map ε.hom := by
  rw [← G.map_comp, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

variable {S : Scheme.{u}} [IsNoetherian S] {X' X Y : FTS S} (h : X' ⟶ X) [IsOpenImmersion h.left]
  (g : X ⟶ Y) (j : CompactificationOf (Over.mk g.left)) {K : Std Y.left} (hK : IsDualizing K)
  {ω : Std X.left} (e : upperShriekDualizing g j hK ≅ ω)

/-- **`f^! ≅ f_new^!` restricts to opens.** For an open immersion `h : X' ⟶ X` and an
identification `e : g^!K ≅ ω`, restricting `g^! ≅ g_new^!` along `h` gives the isomorphism for
`h ≫ g` at the restricted compactification and `Lh^*(e)`, through `Lh^* ∘ g^! ≅ (h ≫ g)^!` and
`Lh^* ∘ g_new^! ≅ (h ≫ g)_new^!`. -/
theorem upperShriekStdIsoFNewShriekOfIso_restrict (M : (plusCoh Y.left).FullSubcategory) :
    (pull h.left).map ((upperShriekStdIsoFNewShriekOfIso g j hK e).hom.app M) ≫
      (fNewShriekRestrictIso h.left g.left (h ≫ g).left rfl ω K).hom.app
        ((plusCoh Y.left).ι.obj M) =
    (upperShriekStdRestrictIso h g j).hom.app M ≫
      (upperShriekStdIsoFNewShriekOfIso (h ≫ g) (j.precompOpen h.left) hK
        ((upperShriekDualizingRestrictIso h g j hK).symm ≪≫ (pull h.left).mapIso e)).hom.app M := by
  have F1 := (relativeDualIsoSheafHom ω).inv.naturality ((pull g.left).op.map
    ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app ((plusCoh Y.left).ι.obj M)))
  have F2 := (relativeDualIsoSheafHom ω).inv_hom_id_app ((pull g.left).op.obj
    ((dualInto K).rightOp.obj ((plusCoh Y.left).ι.obj M)))
  have F3 := pullSheafHomMap_naturality h.left ((pull g.left).map
    ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app ((plusCoh Y.left).ι.obj M)).unop) ω
  have F8 := (relativeDualIsoSheafHom ((pull h.left).obj ω)).inv.naturality
    ((NatIso.op (pullCompIso h.left g.left (h ≫ g).left rfl)).inv.app
      ((dualInto K).rightOp.obj ((plusCoh Y.left).ι.obj M)))
  have F10 := sheafHom_map_comp_app_eq _ _ _ _
    ((pullCompIso h.left g.left (h ≫ g).left rfl).inv.naturality
      ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app
        ((plusCoh Y.left).ι.obj M)).unop).symm
    ((pull h.left).obj ω)
  have F7 := pullSheafHomMap_naturality_right h.left
    ((pull g.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K)) e.hom
  have F6 := ((sheafHom X'.left).map ((pullCompIso h.left g.left (h ≫ g).left rfl).inv.app
      (((sheafHom Y.left).obj (op M.obj)).obj K)).op).naturality ((pull h.left).map e.hom)
  have F5 := map_hom_comp_map_symm_trans_hom ((sheafHom X'.left).obj
      (op ((pull (h ≫ g).left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))))
    (upperShriekDualizingRestrictIso h g j hK) ((pull h.left).mapIso e)
  have T2 := upperShriekDualityIso_restrict h g j hK M
  have F9 := (relativeDualIsoSheafHom ((pull h.left).obj ω)).inv.naturality
    ((pull (h ≫ g).left).op.map
      ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app ((plusCoh Y.left).ι.obj M)))
  refine upperShriekStdIsoFNewShriekOfIso_restrict_chase (pull h.left) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3 F8.symm F10 F7 F6.symm F5 T2 F9.symm
    (upperShriekStdIsoFNewShriekOfIso_hom_app g j hK e M)
    ?_
    (pullDualIso_hom_app_eq h.left ω _)
    (upperShriekStdIsoFNewShriekOfIso_hom_app (h ≫ g) (j.precompOpen h.left) hK
      ((upperShriekDualizingRestrictIso h g j hK).symm ≪≫ (pull h.left).mapIso e) M)
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (fNewShriekRestrictIso_hom_app h.left g.left (h ≫ g).left rfl ω K ((plusCoh Y.left).ι.obj M)))
    (by heq_congr)))

end Stacks.Duality.NormalizedOnOpens
