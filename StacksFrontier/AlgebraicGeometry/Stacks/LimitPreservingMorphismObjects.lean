module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat

/-!
# Limit preserving 1-morphisms are limit preserving on objects (Stacks 0CMS)

A 1-morphism of categories fibred in groupoids over the big fppf category of a scheme `S` which
is limit preserving in the sense of Stacks 0CMR — its square of filtered colimits of fibre
categories over an affine inverse limit is 2-cartesian — is limit preserving on objects in the
sense of Stacks 06CU: given an object `x` of `𝒳` over the limit `U = lim Uᵢ`, an object `y` of
`𝒴` over a stage `Uᵢ`, and a cartesian morphism `γ : f(x) ⟶ y` over `U ⟶ Uᵢ`, the object `x`
descends to some later stage compatibly with `γ`.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isLimitPreserving`: **Stacks 0CMS**.

## Implementation notes

The proof is the one in the source, written out. The 2-cartesian square of Stacks 0CMR is tested
against the one-object square whose two legs name `x` and the image of `y` in the colimit, and
whose filler is the isomorphism `f(x) ≅ γ^*y` that `γ` supplies, `γ` being cartesian and the
fibres being groupoids. Terminality of the 2-fibre product produces an object `z` of
`colim 𝒳_{Uᵢ}` together with isomorphisms identifying its two images with `x` and with the image
of `y`; the descent asked for is then read off `z` by pushing it down to a stage.

Pushing down to a stage is where the colimit's construction enters, and it is the content of
`StacksFrontier.CategoryTheory.Limits.FilteredColimitCat`: `z` comes from some stage
(`CategoryTheory.Cat.exists_stage_obj_of_colimit`), and the isomorphism identifying its image
with the image of `y` comes from a common later stage
(`CategoryTheory.Cat.exists_stage_map_of_colimit`); the index category is cofiltered, so its
opposite — the shape of the diagram of fibres — is filtered and both apply.

Everything is then transported back from the strict split fibres of Stacks 004A, in which the
colimit is formed, to the fibres themselves, through the evaluation equivalence of Stacks 07XL
and the base-change comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`. The pinning conditions on the
2-cell of the square of Stacks 0CMR are exactly what makes that transport possible: without them
the filler of the square would be unrelated to `f`.

The local `implicit_reducible` attributes are what let the slice and `AsSmall` projections be
seen through; see the root-cause notes in `StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting`
for the same phenomenon.

## References

* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Bicategory.InducedBicategory
  AsSmall.up AsSmall.down

/-- **Stacks 0CMS.** A limit preserving 1-morphism of categories fibred in groupoids over the big
fppf category of `S` is limit preserving on objects: every object over an affine inverse limit,
with a cartesian comparison to an object at a finite stage, descends to a later stage. -/
@[stacks 0CMS, stacks 0CMV "the implication (1) ⇒ (2), which holds here without the \
representability hypothesis that Tag 0CMV carries, and for index categories in any universe. The \
whole three-part equivalence is \
`AlgebraicGeometry.Stack.isLimitPreserving_tfae`, for index categories in the universe of the \
schemes"]
theorem isLimitPreservingOnObjects_of_isLimitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLimitPreserving.{u, v, w, uX, vX} B S hS f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, vX, uX}
      B S hS 𝒳 𝒴 f := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  dsimp [BigFppfOver.IsLimitPreservingOnObjects]
  intro I hI _ D c hc i y x γ hγ
  dsimp [IsLimitPreserving] at hf
  specialize hf I D c hc
  rcases hf with ⟨T, H, η, hT⟩
  rcases hT with ⟨hStage, hH, hη, hSquare⟩
  rcases hSquare with ⟨hTerminal⟩
  let inc := BigAffineFppf.inclusion B S hS
  let E := D ⋙ inc
  let d := inc.mapCone c
  let pX := 𝒳.val.p
  let pY := 𝒴.val.p
  let F := CatFiberedInGroupoids.homFunctor f
  let hF := CatFiberedInGroupoids.homFunctor_comp_p f
  let FX := Deformation.Artin.fiberDiagram pX E
  let FY := Deformation.Artin.fiberDiagram pY E
  let lhs := AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
    Functor.fiberFunctorOfCompEq hF d.pt ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}
  let KY := Deformation.Artin.colimitComparison pY E d ⋙
    AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}
  let a := (Functor.fiberFunctorOfCompEq hF d.pt).obj x
  let ySplit : pY.SplitFiber (E.obj i) := ⟨E.obj i, y, 𝟙 _⟩
  let ySmall := AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ySplit
  let cmpX := Deformation.Artin.colimitComparison pX E d
  let cmpY := Deformation.Artin.colimitComparison pY E d
  have ey : cmpY.obj ((Limits.colimit.ι FY (op i)).toFunctor.obj ySmall) =
      pY.pullbackFiber y (d.π.app i ≫ 𝟙 _) :=
    Functor.congr_obj (Deformation.Artin.colimitComparison_ι pY E d i) ySmall
  let : pY.IsHomLift (d.π.app i ≫ 𝟙 _) γ := by simpa [d, inc] using hγ.toIsHomLift
  let lift := Functor.toPullbackFiber pY a y (d.π.app i ≫ 𝟙 _) γ
  let := 𝒴.2.fiber_isGroupoid d.pt
  let eFiber := asIso lift ≪≫ (eqToIso ey).symm
  let eSmall := AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.mapIso eFiber
  let : Category.{max v w vX (u + 1) uX u, max v w vX (u + 1) uX u}
      (PUnit.{max v w vX (u + 1) uX u + 1}) :=
    { Hom := fun _ _ => PUnit.{max v w vX (u + 1) uX u + 1}
      id := fun _ => PUnit.unit
      comp := fun _ _ => PUnit.unit
      id_comp := by intro X Y f; cases f; rfl
      comp_id := by intro X Y f; cases f; rfl
      assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl }
  let I₀ := PUnit.{max v w vX (u + 1) uX u + 1}
  let testFst : I₀ ⥤ AsSmall (pX.Fiber d.pt) :=
    (Functor.const I₀).obj
      (AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj x)
  let testSnd : I₀ ⥤ (Limits.colimit FY : Cat) :=
    (Functor.const I₀).obj
      ((Limits.colimit.ι FY (op i)).toFunctor.obj ySmall)
  let αtest : testFst ⋙ lhs ≅ testSnd ⋙ KY :=
    NatIso.ofComponents (fun _ => eSmall) (by
      intro j j' g
      simp [testFst, testSnd, Functor.const])
  let Q : Bicategory.TwoCommSq lhs.toCatHom KY.toCatHom :=
    { pt := Cat.of I₀
      fst := Functor.toCatHom testFst
      snd := Functor.toCatHom testSnd
      iso := Cat.Hom.isoMk αtest }
  obtain ⟨pre, _hpre⟩ := Quotient.exists_rep (hTerminal.from Q)
  let z := pre.hom.toFunctor.obj PUnit.unit
  let xSmall := AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj x
  let hx : xSmall ≅ (Deformation.Artin.colimitComparison pX E d ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).obj z :=
    (Cat.Hom.toNatIso pre.isoFst).app PUnit.unit
  let hy : (Limits.colimit.ι FY (op i)).toFunctor.obj ySmall ≅ H.obj z :=
    (Cat.Hom.toNatIso pre.isoSnd).app PUnit.unit
  have hcompat : eSmall.hom ≫ KY.map hy.hom = lhs.map hx.hom ≫ (η.app z).hom := by
    simpa [Q, αtest, eSmall, hx, hy, lhs, KY, z, hF, pX, pY, E, d, inc] using
      congrArg (fun α => α.toNatTrans.app PUnit.unit) pre.compat
  have hcompat' : (η.app z).hom ≫ KY.map hy.inv = lhs.map hx.inv ≫ eSmall.hom := by
    apply (cancel_epi (lhs.map hx.hom)).1
    calc
      lhs.map hx.hom ≫ ((η.app z).hom ≫ KY.map hy.inv) =
          (lhs.map hx.hom ≫ (η.app z).hom) ≫ KY.map hy.inv :=
        (Category.assoc _ _ _).symm
      _ = (eSmall.hom ≫ KY.map hy.hom) ≫ KY.map hy.inv :=
        congrArg (fun q => q ≫ KY.map hy.inv) hcompat.symm
      _ = lhs.map hx.hom ≫ (lhs.map hx.inv ≫ eSmall.hom) := by
        simp only [Category.assoc, Iso.map_hom_inv_id, Functor.comp_obj,
          Iso.map_hom_inv_id_assoc]
        exact Category.comp_id eSmall.hom
  let β₀ := AsSmall.down.map hx.inv
  have hcompatFiber : AsSmall.down.map (η.app z).hom ≫ cmpY.map hy.inv =
      (Functor.fiberFunctorOfCompEq hF d.pt).map β₀ ≫ eFiber.hom :=
    congrArg (fun q => AsSmall.down.map q) hcompat'
  obtain ⟨k₀, a₀, ha₀⟩ := Cat.exists_stage_obj_of_colimit.{max (u + 1) uX vX, v, w} FX z
  let b₀ := (T.app k₀).toFunctor.obj a₀
  have hb₀ : H.obj z = (colimit.ι FY k₀).toFunctor.obj b₀ := by
    rw [hH, ← ha₀]
    exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (ι_colimMap T k₀)) a₀
  let fcol := eqToHom hb₀.symm ≫ hy.inv
  obtain ⟨l, s, t, g, hg⟩ := Cat.exists_stage_map_of_colimit.{max (u + 1) uX vX, v, w}
    FY k₀ (op i) b₀ ySmall fcol
  let m := l.unop
  let xm := (FX.map s).toFunctor.obj a₀
  let xs : pX.SplitFiber (E.obj m) := AsSmall.down.{vX, max (u + 1) uX, max v w}.obj xm
  let ys := splitFiberMap B S hS f (E.obj m) |>.obj xs
  let yt : pY.SplitFiber (E.obj m) :=
    AsSmall.down.{vX, max (u + 1) uX, max v w}.obj ((FY.map t).toFunctor.obj ySmall)
  have hb : (FY.map s).toFunctor.obj b₀ = AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys :=
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (T.naturality s)) a₀).symm.trans
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor (hStage m)) xm)
  let gs : ys ⟶ yt := AsSmall.down.{vX, max (u + 1) uX, max v w}.map (eqToHom hb.symm ≫ g)
  have hz : (colimit.ι FX l).toFunctor.obj xm = z :=
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w FX s)) a₀).trans ha₀
  let xU := pX.pullbackFiber xs.obj (d.π.app m ≫ xs.hom)
  have ex : cmpX.obj z = xU := by
    rw [← hz]
    exact Functor.congr_obj (Deformation.Artin.colimitComparison_ι pX E d m) xm
  let βf : xU ⟶ x := eqToHom ex.symm ≫ β₀
  let β := Functor.Fiber.fiberInclusion.map βf
  let δ := Functor.pullbackFiberProj xs.obj xs.hom (d.π.app m)
  let hFib := isFibredOneMorphism B S hS f
  let γ' := Functor.Fiber.fiberInclusion.map
    ((hFib.mapPullbackFiberIso xs.obj xs.hom).inv ≫
      Functor.SplitFiber.toFiberHom gs) ≫ yt.proj
  have : pY.IsHomLift (E.map t.unop) γ' := by
    have h : pY.IsHomLift (𝟙 (E.obj m) ≫ yt.hom) γ' := by
      dsimp only [γ']
      infer_instance
    change pY.IsHomLift (𝟙 _ ≫ (E.map t.unop ≫ 𝟙 _)) γ' at h
    simpa only [Category.id_comp, Category.comp_id] using h
  refine ⟨m, t.unop, xs.toFiber, xU, δ, β, γ', ?_, ?_, ?_, ?_, ?_⟩
  · let : pX.IsHomLift (d.π.app m) δ := by dsimp [δ]; infer_instance
    simpa [d, inc] using 𝒳.2.isStronglyCartesian_homLift (d.π.app m) δ
  · exact βf.2
  · have : IsIso βf := (𝒳.2.fiber_isGroupoid d.pt).all_isIso βf
    exact Functor.map_isIso Functor.Fiber.fiberInclusion βf
  · exact 𝒴.2.isStronglyCartesian_homLift (E.map t.unop) γ'
  · change F.map δ ≫ γ' = F.map β ≫ γ
    let fu := Functor.fiberFunctorOfCompEq hF d.pt
    let yu := (Functor.SplitFiber.restrict pY (d.π.app m)).obj ys
    let ytu := (Functor.SplitFiber.restrict pY (d.π.app m)).obj yt
    let gu := (Functor.SplitFiber.restrict pY (d.π.app m)).map gs
    let ebc := hFib.mapPullbackFiberIso xs.obj (d.π.app m ≫ xs.hom)
    have hHstage : H.obj z = (colimit.ι FY l).toFunctor.obj
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys) := by
      rw [hH, ← hz]
      exact (Functor.congr_obj (congrArg Cat.Hom.toFunctor (ι_colimMap T l)) xm).trans
        (congrArg (colimit.ι FY l).toFunctor.obj
          (Functor.congr_obj (congrArg Cat.Hom.toFunctor (hStage m)) xm))
    have eu : cmpY.obj (H.obj z) = yu.toFiber :=
      (congrArg cmpY.obj hHstage).trans
        (Functor.congr_obj (Deformation.Artin.colimitComparison_ι pY E d m)
          (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys))
    have et : cmpY.obj ((colimit.ι FY (op i)).toFunctor.obj ySmall) = ytu.toFiber :=
      (congrArg cmpY.obj
        (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w FY t)) ySmall).symm).trans
        (Functor.congr_obj (Deformation.Artin.colimitComparison_ι pY E d m)
          ((FY.map t).toFunctor.obj ySmall))
    have hηz : HEq (AsSmall.down.map (η.app z).hom) ebc.inv := by
      have h := hη m xs
      change HEq (AsSmall.down.map (η.app ((colimit.ι FX l).toFunctor.obj xm)).hom)
        ebc.inv at h
      rwa [hz] at h
    have hηeq := Cat.transport_hom_of_heq (congrArg fu.obj ex) eu hηz
    have hgs : HEq ((colimit.ι FY l).toFunctor.map
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.map gs)) hy.inv := by
      have hmc :=
        (Functor.map_comp (colimit.ι FY l).toFunctor (eqToHom hb.symm) g).trans
          (congrArg (fun k => k ≫ (colimit.ι FY l).toFunctor.map g)
            (eqToHom_map (colimit.ι FY l).toFunctor hb.symm))
      refine HEq.trans (heq_of_eq hmc) ?_
      exact (eqToHom_comp_heq _ _).trans
        (hg.trans (eqToHom_comp_heq _ _))
    have hgu : HEq (cmpY.map hy.inv) gu := by
      have h := Cat.map_heq_of_eq cmpY hHstage.symm
        (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w FY t)) ySmall) hgs
      exact h.symm.trans (Functor.hcongr_hom
        (Deformation.Artin.colimitComparison_ι pY E d m)
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.map gs))
    have hgeq := Cat.transport_hom_of_heq eu et hgu
    have hcomb : ebc.inv ≫ gu = fu.map βf ≫ eFiber.hom ≫ eqToHom et := by
      rw [← cancel_epi (eqToHom (congrArg fu.obj ex)), ← Category.assoc, ← hηeq,
        Category.assoc, ← hgeq, ← Category.assoc, hcompatFiber]
      simp only [fu, βf, Functor.map_comp, eqToHom_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have he : F.map δ ≫ Functor.Fiber.fiberInclusion.map
        (hFib.mapPullbackFiberIso xs.obj xs.hom).inv =
        Functor.Fiber.fiberInclusion.map ebc.inv ≫
          Functor.pullbackFiberProj ys.obj ys.hom (d.π.app m) := by
      apply Functor.IsStronglyCartesian.ext pY ys.hom ys.proj (d.π.app m)
      simp only [Category.assoc, Functor.pullbackFiberProj_fac]
      change F.map δ ≫ Functor.Fiber.fiberInclusion.map
          (hFib.mapPullbackFiberIso xs.obj xs.hom).inv ≫
          Functor.IsPreFibered.pullbackMap ys.obj.2 xs.hom = _
      rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
        ← F.map_comp, Functor.pullbackFiberProj_fac]
      exact (Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac
        hFib xs.obj (d.π.app m ≫ xs.hom)).symm
    have hproj : Functor.Fiber.fiberInclusion.map
        (eFiber.hom ≫ eqToHom et) ≫ ytu.proj = γ := by
      have ep : d.π.app m ≫ yt.hom = d.π.app i ≫ 𝟙 _ := by
        change d.π.app m ≫ (E.map t.unop ≫ 𝟙 _) = _
        rw [← Category.assoc, d.w t.unop]
      dsimp only [eFiber, Iso.trans_hom, asIso_hom, Iso.symm_hom, eqToIso.inv]
      rw [Category.assoc, eqToHom_trans, Functor.map_comp, Category.assoc, eqToHom_map]
      change Functor.Fiber.fiberInclusion.map lift ≫ eqToHom _ ≫
        Functor.IsPreFibered.pullbackMap y.2 (d.π.app m ≫ yt.hom) = γ
      exact (congrArg (fun k => Functor.Fiber.fiberInclusion.map lift ≫ k)
          (Functor.eqToHom_comp_pullbackMap y ep.symm _)).trans
        (Functor.toPullbackFiber_fac pY a y _ γ)
    dsimp only [γ']
    rw [Functor.map_comp, Category.assoc, ← Category.assoc (F.map δ), he, Category.assoc,
      ← Functor.SplitFiber.restrictHom_fac (p := pY)
      (d.π.app m) (o := ys) (o' := yt) (Functor.SplitFiber.toFiberHom gs)]
    change Functor.Fiber.fiberInclusion.map ebc.inv ≫
      Functor.Fiber.fiberInclusion.map gu ≫ ytu.proj = _
    rw [← Functor.map_comp_assoc, hcomb, Functor.map_comp, Category.assoc, hproj]
    rfl

end AlgebraicGeometry.Stack

end
