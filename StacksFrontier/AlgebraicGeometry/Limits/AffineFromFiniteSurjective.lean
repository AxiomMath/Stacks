module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClauseThree.GenericStalkInput
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.FiniteIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Approximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Affineness of the target of a finite surjective morphism

A scheme receiving a finite surjective morphism from an affine scheme is affine.

## Main results

* `Stacks.AffineFromFiniteSurjective.exists_isAffine_finitePresentation_of_isFinite_surjective`:
  a finite surjective morphism with affine source may be replaced by one which is in addition of
  finite presentation.
* `Stacks.AffineFromFiniteSurjective.exists_isLimit_isNoetherian`: a quasi-compact and
  quasi-separated scheme is the inverse limit of a directed system of Noetherian schemes with
  affine transition morphisms.
* `Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective`: the target of a finite
  surjective morphism of schemes with affine source is affine.

## References

* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
* [Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AffineFromFiniteSurjective

/-! ### Base change along a composite -/

/-- Base change along a composite is base change along its two factors in turn: a property of
morphisms stable under base change which holds after base change along `a` holds after base
change along `b ≫ a`. -/
theorem overPullbackMap_comp
    {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {S T U : C} (a : T ⟶ S) (b : U ⟶ T)
    {X Y : Over S} (f : X ⟶ Y) (hf : P ((Over.pullback a).map f).left) :
    P ((Over.pullback (b ≫ a)).map f).left := by
  let e := Over.pullbackComp b a
  let α := (Over.forget U).mapIso (e.app X)
  let β := (Over.forget U).mapIso (e.app Y)
  have hn : ((Over.pullback (b ≫ a)).map f).left ≫ β.hom =
      α.hom ≫ ((Over.pullback a ⋙ Over.pullback b).map f).left :=
    congrArg Over.Hom.left (e.hom.naturality f)
  exact (P.arrow_mk_iso_iff (Arrow.isoMk α β hn.symm)).mpr
    (P.overPullbackMap b ((Over.pullback a).map f) hf)

/-! ### Reduction to a morphism of finite presentation -/

/-- A finite surjective morphism with affine source onto a quasi-compact and quasi-separated
scheme may be replaced by one which is in addition of finite presentation. -/
theorem exists_isAffine_finitePresentation_of_isFinite_surjective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Surjective f] [IsAffine X] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S),
      IsAffine X' ∧ IsFinite f' ∧ FinitePresentation f' ∧ Surjective f' := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨I, _, _, _, D, t, p, hlim, hcompat, hstage, htrans, hproj⟩ :=
    exists_isLimit_finitePresentation_closedImmersion f
  have hfac : ∀ i : I, p.app (Opposite.op i) ≫ t.app (Opposite.op i) = f := fun i => by
    simpa using congrArg (fun η => η.app (Opposite.op i)) hcompat
  have hcs : ∀ i : I, CompactSpace (D.obj (Opposite.op i)) := fun i => (hstage _).2.1
  have hqs : ∀ i : I, QuasiSeparatedSpace (D.obj (Opposite.op i)) := fun i => (hstage _).2.2
  have hft : ∀ i : I, LocallyOfFiniteType (t.app (Opposite.op i)) := fun i => by
    have : LocallyOfFinitePresentation (t.app (Opposite.op i)) :=
      (hstage _).1.locallyOfFinitePresentation
    infer_instance
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp
    (eventually_isFinite_of_isLimit_of_isIntegral D t (Cone.mk X p) hlim f
      (fun i => (hfac i).symm)
      (fun {_ _} h => by have := htrans (homOfLE h).op; infer_instance)
      (fun {_ _} h => by have := htrans (homOfLE h).op; infer_instance))
  have haff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g ↦ by
    have := htrans g
    infer_instance
  have hcs' : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) := fun i ↦ hcs i.unop
  have hqs' : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i ↦ hqs i.unop
  have : IsAffine (Cone.mk X p).pt := ‹IsAffine X›
  obtain ⟨a, ha⟩ := Scheme.exists_isAffine_of_isLimit D (Cone.mk X p) hlim
  obtain ⟨k, hak, hik⟩ := directed_of (· ≤ ·) a.unop i₀
  have hkaff : IsAffine (D.obj (Opposite.op k)) := by
    have : IsAffine (D.obj (Opposite.op a.unop)) := ha
    exact isAffine_of_isAffineHom (D.map (homOfLE hak).op)
  refine ⟨D.obj (Opposite.op k), t.app (Opposite.op k), hkaff, hi₀ k hik, (hstage _).1, ?_⟩
  have : Surjective (p.app (Opposite.op k) ≫ t.app (Opposite.op k)) := hfac k ▸ inferInstance
  exact Surjective.of_comp (p.app (Opposite.op k)) (t.app (Opposite.op k))

/-! ### The Noetherian approximation of the base -/

/-- A quasi-compact and quasi-separated scheme is the inverse limit of a directed system of
Noetherian schemes whose transition morphisms are affine. -/
theorem exists_isLimit_isNoetherian (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (A : Jᵒᵖ ⥤ Scheme.{u}) (pS : (Functor.const Jᵒᵖ).obj S ⟶ A)
      (_ : IsLimit (Cone.mk S pS)),
      (∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (A.map g)) ∧ ∀ i, IsNoetherian (A.obj i) := by
  let Q := LimitFPObjectDescent.finiteTypeSchemeApproximation S
  exact ⟨Q.indexType, Q.indexPreorder, Q.indexNonempty, Q.indexDirected, Q.stages, Q.projection,
    Q.limit, Q.transition_affine, fun i ↦ isNoetherian_of_locallyOfFiniteType_terminalFrom _
      (Q.stage_locallyOfFiniteType i) (Q.stage_quasiCompact i)⟩

/-! ### Affineness of the target -/

/-- The target of a finite surjective morphism of schemes is affine when
its source is affine. -/
@[stacks 01ZT]
theorem isAffine_of_finite_surjective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Surjective f] [IsAffine X] : IsAffine S := by
  have : IsIntegralHom f :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp inferInstance).1
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_surjective_universallyClosed f
  have : CompactSpace S := ⟨f.surjective.range_eq ▸ isCompact_range f.continuous⟩
  obtain ⟨X', f', hX'aff, hf'fin, hf'fp, hf'surj⟩ :=
    exists_isAffine_finitePresentation_of_isFinite_surjective f
  obtain ⟨J, _, _, _, A, pS, hlimS, htr, hNA⟩ := exists_isLimit_isNoetherian S
  let cS : Cone A := Cone.mk S pS
  have hcS : IsLimit cS := hlimS
  have hcompA : ∀ i : Jᵒᵖ, CompactSpace (A.obj i) := fun i ↦ (hNA i).toCompactSpace
  have hqsA : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (A.obj i) := fun i ↦ by
    have := hNA i
    infer_instance
  let X₀ : Over S := Over.mk f'
  obtain ⟨j, Xj, hfpj, hXj⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation A cS hcS X₀ hf'fp
  have : LocallyOfFinitePresentation Xj.hom := hfpj.1
  have : QuasiCompact Xj.hom := hfpj.2.1
  have : QuasiSeparated Xj.hom := hfpj.2.2
  have : CompactSpace Xj.left := QuasiCompact.compactSpace_of_compactSpace Xj.hom
  have : QuasiSeparatedSpace Xj.left := quasiSeparatedSpace_of_quasiSeparated Xj.hom
  let Yj : Over (A.obj j) := Over.mk (𝟙 (A.obj j))
  have : CompactSpace Yj.left := hcompA j
  have : QuasiSeparatedSpace Yj.left := hqsA j
  let fj : Xj ⟶ Yj := Over.homMk Xj.hom (by rfl)
  have : LocallyOfFinitePresentation fj.left := hfpj.1
  have : LocallyOfFiniteType fj.left := inferInstanceAs (LocallyOfFiniteType Xj.hom)
  let P := Over.pullback (cS.π.app j)
  let Xlim := P.obj Xj
  let Ylim := P.obj Yj
  let M := P.map fj
  obtain ⟨eX⟩ := hXj
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget S).map eX.hom))
  have : IsIso Ylim.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 (A.obj j)) (cS.π.app j)))
  have hcmp : eX.hom.left ≫ M.left ≫ Ylim.hom = X₀.hom := by
    rw [M.w, eX.hom.w]
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.respectsIso_of_isStableUnderComposition (P := @IsFinite)
      fun _ _ _ _ ↦ inferInstance
  have hM : ∀ (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso], Q f' → Q M.left :=
    fun Q _ h ↦ (Q.cancel_right_of_respectsIso M.left Ylim.hom).mp
      ((Q.cancel_left_of_respectsIso eX.hom.left (M.left ≫ Ylim.hom)).mp (hcmp ▸ h))
  have : IsFinite M.left := hM @IsFinite hf'fin
  have : Surjective M.left := hM @Surjective hf'surj
  obtain ⟨k, g, hfinite⟩ := exists_isFinite_baseChange_of_isLimit A cS hcS j Xj Yj fj
  obtain ⟨l, h, hsurj⟩ :=
    exists_surjective_baseChange_of_surjective_limitBaseChange A cS hcS j Xj Yj fj
  let qIndex : Bool → Jᵒᵖ := fun
    | true => k
    | false => l
  let qArrow : (b : Bool) → qIndex b ⟶ j := fun
    | false => h
    | true => g
  obtain ⟨m, gm, hm, hh⟩ := IsCofiltered.wideCospan qArrow
  have hfiniteM : IsFinite ((Over.pullback (A.map gm)).map fj).left := by
    have hhtrue : hm true ≫ g = gm := hh true
    rw [← hhtrue, A.map_comp]
    exact overPullbackMap_comp (@IsFinite) (A.map g) (A.map (hm true)) fj hfinite
  have hsurjM : Surjective ((Over.pullback (A.map gm)).map fj).left := by
    have hhfalse : hm false ≫ h = gm := hh false
    rw [← hhfalse, A.map_comp]
    exact overPullbackMap_comp (@Surjective) (A.map h) (A.map (hm false)) fj hsurj
  let Xm := (Over.pullback (A.map gm)).obj Xj
  let Ym := (Over.pullback (A.map gm)).obj Yj
  let fm : Xm ⟶ Ym := (Over.pullback (A.map gm)).map fj
  have : IsFinite fm.left := hfiniteM
  have : Surjective fm.left := hsurjM
  have : IsIso Ym.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 (A.obj j)) (A.map gm)))
  have : IsFinite Xm.hom := by
    simpa [Over.w] using (inferInstance : IsFinite (fm.left ≫ Ym.hom))
  have : Surjective Xm.hom := by
    simpa [Over.w] using (inferInstance : Surjective (fm.left ≫ Ym.hom))
  have : CompactSpace Xm.left := QuasiCompact.compactSpace_of_compactSpace Xm.hom
  have : QuasiSeparatedSpace Xm.left := quasiSeparatedSpace_of_quasiSeparated Xm.hom
  have hbc : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange] {Y Z : Scheme.{u}}
      (g : Y ⟶ Z), Q.IsStableUnderBaseChangeAlong g :=
    fun Q _ _ _ g ↦ ⟨fun pb hP ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hP⟩
  have := hbc @IsAffineHom Xm.hom
  let Dtail : Over m ⥤ Scheme.{u} :=
    Over.post A ⋙ Over.pullback Xm.hom ⋙ Over.forget Xm.left
  let ctail : Cone Dtail :=
    (Over.pullback Xm.hom ⋙ Over.forget Xm.left).mapCone ((Over.conePost A m).obj cS)
  have hctail : IsLimit ctail :=
    isLimitOfPreserves (Over.pullback Xm.hom ⋙ Over.forget Xm.left)
      (Over.isLimitConePost m hcS)
  have : IsAffine ctail.pt := by
    let eComp := Over.pullbackComp (cS.π.app m) (A.map gm)
    let eBase := (Over.forget S).mapIso (eComp.app Xj)
    let eEq := pullback.congrHom (f₁ := Xj.hom) (f₂ := Xj.hom)
      (g₁ := cS.π.app m ≫ A.map gm) (g₂ := cS.π.app j) rfl (cS.w gm)
    let eTail : ctail.pt ≅ Xlim.left := by
      simpa [ctail, Dtail, Xm, Xlim, P] using
        ((pullbackSymmetry (cS.π.app m) Xm.hom) ≪≫ eBase.symm ≪≫ eEq)
    have : IsAffine X₀.left := hX'aff
    have hIso : ctail.pt ≅ X₀.left := eTail ≪≫ (Over.forget S).mapIso eX.symm
    exact IsAffine.of_isIso hIso.hom
  have hXₐ : ∀ a : Over m, IsAffineHom ((Over.pullback Xm.hom).obj ((Over.post A).obj a)).hom :=
    fun a ↦ MorphismProperty.pullback_snd (P := @IsAffineHom) (A.map a.hom) Xm.hom (htr a.hom)
  have : ∀ a : Over m, CompactSpace (Dtail.obj a) := fun a ↦
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback Xm.hom).obj ((Over.post A).obj a)).hom
  have : ∀ a : Over m, QuasiSeparatedSpace (Dtail.obj a) := fun a ↦
    quasiSeparatedSpace_of_quasiSeparated ((Over.pullback Xm.hom).obj ((Over.post A).obj a)).hom
  have : ∀ {a b : Over m} (q : a ⟶ b), IsAffineHom (Dtail.map q) := fun q ↦
    MorphismProperty.overPullbackMap (P := @IsAffineHom) Xm.hom ((Over.post A).map q) (htr q.left)
  obtain ⟨a, ha⟩ := Scheme.exists_isAffine_of_isLimit Dtail ctail hctail
  let prₐ : Dtail.obj a ⟶ A.obj a.left := pullback.fst (A.map a.hom) Xm.hom
  have := hbc @IsFinite (A.map a.hom)
  have := hbc @Surjective (A.map a.hom)
  have : IsFinite prₐ :=
    MorphismProperty.pullback_fst (P := @IsFinite) (A.map a.hom) Xm.hom inferInstance
  have : Surjective prₐ :=
    MorphismProperty.pullback_fst (P := @Surjective) (A.map a.hom) Xm.hom inferInstance
  have : IsAffine (A.obj a.left) :=
    Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective prₐ
  have hLaterAffine : ∀ b : Over a.left, IsAffine (A.obj b.left) := fun b ↦ by
    have : IsAffineHom (A.map b.hom) := htr b.hom
    exact isAffine_of_isAffineHom (A.map b.hom)
  let F := Over.post A ⋙ Over.forget (A.obj a.left)
  have : ∀ b : Over a.left, IsAffine (F.obj b) := hLaterAffine
  exact Scheme.isAffine_of_isLimit
    ((Over.forget (A.obj a.left)).mapCone ((Over.conePost A a.left).obj cS))
    (isLimitOfPreserves (Over.forget (A.obj a.left)) (Over.isLimitConePost a.left hcS))

end Stacks.AffineFromFiniteSurjective

end
