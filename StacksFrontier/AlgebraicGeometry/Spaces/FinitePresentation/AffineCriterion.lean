module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving

/-!
# The affine-limit criterion for relative limit preservation

A transformation of set-valued presheaves on the big fppf site over a scheme is relatively
limit preserving exactly when, for every cofiltered inverse limit of affine objects, the
square comparing the colimit of the source values with the value at the limit is cartesian.
This replaces the quantification over section fibres by a single cartesian square, and is
the form in which relative limit preservation is checked in practice.

## Main results

* `AlgebraicGeometry.relativelyLimitPreserving_iff_affineLimit_isPullback` is the
  affine-limit criterion.

## Implementation notes

The four corners of the square are the canonical colimits and the evaluations of the two
presheaves, after applying `CategoryTheory.uliftFunctor`. The horizontal arrows come from
the limit cone and the left vertical arrow is induced by the transformation. The indexing
category and its morphisms may lie in independent universes; index objects live in
`max w w'`, as in `AlgebraicGeometry.LimitPreserving`, so passing to `Over i` keeps the
same indexing size when a system is restricted to a stage. Lifting the values to the
maximum of the value and index universes makes the colimits available without a
universe-inclusion hypothesis, and the lift preserves and reflects both colimits and
pullbacks of sets.

## References

* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' wm z z'

namespace AlgebraicGeometry

/-- The functor from the objects over an index `i` to the objects over `D.obj i`, sending
`t ⟶ i` to the image `D.map t.hom`. It restricts a system to the stage `i`. -/
private def tailOverFunctor
    {C : Type z} [Category.{z'} C]
    {I : Type w} [Category.{w'} I] (D : I ⥤ C) (i : I) :
    Over i ⥤ Over (D.obj i) where
  obj t := Over.mk (D.map t.hom)
  map {t t'} f := Over.homMk (D.map f.left) (by
    change D.map f.left ≫ D.map t'.hom = D.map t.hom
    rw [← D.map_comp]
    exact congrArg D.map f.w)
  map_id t := by
    apply Over.OverMorphism.ext
    simp
  map_comp {t t' t''} f g := by
    apply Over.OverMorphism.ext
    simp

/-- The cone over `tailOverFunctor D i` whose apex is the leg `c.π.app i` of a cone `c`,
with legs the remaining legs of `c`. -/
private def tailOverCone
    {C : Type z} [Category.{z'} C]
    {I : Type w} [Category.{w'} I]
    {D : I ⥤ C} (c : Cone D) (i : I) :
    Cone (tailOverFunctor D i) where
  pt := Over.mk (c.π.app i)
  π :=
    { app := fun t => Over.homMk (c.π.app t.left) (by
        change c.π.app t.left ≫ D.map t.hom = c.π.app i
        exact c.w t.hom)
      naturality := by
        intro t t' f
        apply Over.OverMorphism.ext
        change (𝟙 _ ≫ c.π.app t'.left) = c.π.app t.left ≫ D.map f.left
        simpa only [Category.id_comp] using (c.w f.left).symm }

/-- The restriction of a limit cone to the stage `i` is again a limit cone, because the
forgetful functor from the objects over `i` is initial. -/
private noncomputable def tailOverCone_map_isLimit
    {C : Type z} [Category.{z'} C]
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (T : C ⥤ Scheme.{u}) (D : I ⥤ C) (c : Cone D)
    (hc : IsLimit (T.mapCone c)) (i : I) :
    IsLimit ((Over.forget (D.obj i) ⋙ T).mapCone (tailOverCone c i)) := by
  let E := Over.forget i
  have : Functor.Initial E := Over.initial_forget i
  have h := (Functor.Initial.isLimitWhiskerEquiv E (T.mapCone c)).symm hc
  change IsLimit (Cone.whisker E (T.mapCone c)) at h
  exact h

/-- The fibre of a map of types over a point is the pullback of the map along that point. -/
private theorem isPullback_subtype_fiber {A B : Type v} (φ : A ⟶ B) (b : B) :
    IsPullback (TypeCat.ofHom (Subtype.val : {x // φ x = b} → A))
      (TypeCat.ofHom fun _ : {x // φ x = b} => PUnit.unit) φ
      (TypeCat.ofHom fun _ : PUnit => b) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, fun x x' hx => Subtype.ext hx.1, fun x z hx => ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  ext x
  exact x.2

/-- If the affine-limit comparison square of a transformation is cartesian for a given
cofiltered system over an object, then the section fibre over any target section sends that
system's limit cone to a colimit cocone. -/
private theorem sectionFiber_colimit_isColimit_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) [UnivLE.{w, v}]
    (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X))
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (D : I ⥤ Over X) (c : Cone D)
    (hSq : IsPullback
      (colimit.desc (((D ⋙ Over.forget X).op ⋙ F))
        (F.mapCocone ((Over.forget X).mapCone c).op))
      (colimMap (Functor.whiskerLeft (D ⋙ Over.forget X).op a))
      (a.app (Opposite.op c.pt.left))
      (colimit.desc (((D ⋙ Over.forget X).op ⋙ G))
        (G.mapCocone ((Over.forget X).mapCone c).op))) :
    Nonempty (IsColimit
      ((sectionFiber B S hS a X y).mapCocone c.op)) := by
  let P := D.op ⋙ sectionFiber B S hS a X y
  let Q := (D ⋙ Over.forget X).op ⋙ F
  let R := (D ⋙ Over.forget X).op ⋙ G
  let U := (Functor.const Iᵒᵖ).obj PUnit
  let f : P ⟶ Q :=
    { app := fun i => TypeCat.ofHom fun x : P.obj i => x.1
      naturality := by intro i j g; ext x; rfl }
  let g : P ⟶ U :=
    { app := fun i => TypeCat.ofHom fun _ : P.obj i => PUnit.unit
      naturality := by intro i j f; ext x; rfl }
  let h : Q ⟶ R := Functor.whiskerLeft (D ⋙ Over.forget X).op a
  let k : U ⟶ R :=
    { app := fun i => TypeCat.ofHom fun _ : PUnit =>
        G.map ((D.obj i.unop).hom.op) y
      naturality := by
        intro i j f
        ext x
        change G.map ((D.obj j.unop).hom.op) y =
          G.map ((D.map f.unop).left.op) (G.map ((D.obj i.unop).hom.op) y)
        rw [← G.map_comp_apply, ← op_comp, Over.w (D.map f.unop)] }
  have hStage : IsPullback f g h k := by
    apply IsPullback.of_forall_isPullback_app
    intro i
    exact isPullback_subtype_fiber _ _
  have hColim : IsPullback (colimMap f) (colimMap g) (colimMap h) (colimMap k) :=
    Functor.map_isPullback (colim : (Iᵒᵖ ⥤ Type v) ⥤ Type v) hStage
  let cF := F.mapCocone ((Over.forget X).mapCone c).op
  let cG := G.mapCocone ((Over.forget X).mapCone c).op
  let cP := (sectionFiber B S hS a X y).mapCocone c.op
  let cU : Cocone U :=
    { pt := PUnit
      ι := 𝟙 _ }
  let u : colimit U ⟶ PUnit := colimit.desc U cU
  let t : PUnit ⟶ G.obj (Opposite.op c.pt.left) := TypeCat.ofHom fun _ =>
    G.map c.pt.hom.op y
  have hu : IsIso u := by
    let : IsConnected Iᵒᵖ := IsFiltered.isConnected _
    dsimp [u, U, cU]
    exact (Types.colimitConstPUnitIsoPUnit.{v} Iᵒᵖ).isIso_hom
  let : IsIso u := hu
  have hk : colimMap k ≫ colimit.desc R cG = u ≫ t := by
    apply colimit.hom_ext
    intro i
    have h₁ : colimit.ι U i ≫ colimMap k ≫ colimit.desc R cG =
        k.app i ≫ cG.ι.app i := by
      rw [ι_colimMap_assoc, colimit.ι_desc]
    have h₂ : k.app i ≫ cG.ι.app i = cU.ι.app i ≫ t := by
      ext z
      change G.map ((c.π.app i.unop).left.op) (G.map ((D.obj i.unop).hom.op) y) =
        G.map c.pt.hom.op y
      rw [← G.map_comp_apply, ← op_comp, Over.w (c.π.app i.unop)]
      rfl
    have h₃ : cU.ι.app i ≫ t = colimit.ι U i ≫ u ≫ t := by
      ext z
      simp [cU, u]
    exact h₁.trans (h₂.trans h₃)
  have hOuter : IsPullback
      (colimMap f ≫ colimit.desc Q cF)
      (colimMap g)
      (a.app (Opposite.op c.pt.left))
      (u ≫ t) := by
    simpa [hk, Q, R, cF, cG] using hColim.paste_horiz hSq
  have hUnit : IsPullback (u ≫ t) u (𝟙 _) t :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hTarget : IsPullback
      (colimMap f ≫ colimit.desc Q cF)
      (colimMap g ≫ u)
      (a.app (Opposite.op c.pt.left)) t :=
    hOuter.paste_vert hUnit
  have hFiber : IsPullback
      (TypeCat.ofHom (fun x : (sectionFiber B S hS a X y).obj
        (Opposite.op c.pt) => x.1))
      (TypeCat.ofHom (fun _ : (sectionFiber B S hS a X y).obj
        (Opposite.op c.pt) => PUnit.unit))
      (a.app (Opposite.op c.pt.left)) t := by
    exact isPullback_subtype_fiber _ _
  let e := hTarget.isoIsPullback _ _ hFiber
  have he : e.hom = colimit.desc P cP := by
    apply hFiber.hom_ext
    · rw [hTarget.isoIsPullback_hom_fst]
      apply colimit.hom_ext
      intro i
      ext x
      have hL : colimit.ι P i ≫ colimMap f ≫ colimit.desc Q cF =
          f.app i ≫ cF.ι.app i := by
        rw [ι_colimMap_assoc, colimit.ι_desc]
      have hR : (colimit.ι P i ≫ colimit.desc P cP) ≫
          TypeCat.ofHom (fun z : cP.pt => z.1) = f.app i ≫ cF.ι.app i := by
        rw [colimit.ι_desc]
        ext z
        rfl
      exact congrArg (fun φ => φ x) (hL.trans hR.symm)
    · rw [hTarget.isoIsPullback_hom_snd]
      apply colimit.hom_ext
      intro i
      ext x
  have hIso : IsIso (colimit.desc P cP) := by
    rw [← he]
    infer_instance
  let : IsIso (colimit.desc P cP) := hIso
  let eCoc : colimit.cocone P ≅ cP := Cocone.ext (asIso (colimit.desc P cP)) (by
    intro i
    simp)
  exact ⟨(colimit.isColimit P).ofIsoColimit eCoc⟩

/-- Lifting the values of a section fibre to a larger universe agrees, at each object, with
the section fibre of the lifted transformation at the lifted section. -/
private def sectionFiberUliftEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X)) (Y : (Over X)ᵒᵖ) :
    ULift ((sectionFiber B S hS a X y).obj Y) ≃
      (sectionFiber B S hS
        (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{wm, v}))
        X (ULift.up y)).obj Y := by
  refine Equiv.mk (fun z => ⟨ULift.up z.down.1, ?_⟩)
    (fun z => ⟨⟨z.1.down, ?_⟩⟩) ?_ ?_
  · change ULift.up (a.app (Opposite.op Y.unop.left) z.down.1) =
      ULift.up (G.map Y.unop.hom.op y)
    exact congrArg ULift.up z.down.2
  · exact ULift.ext_iff.mp z.2
  · intro z
    cases z
    rfl
  · intro z
    apply Subtype.ext
    apply ULift.ext
    rfl

/-- The section fibre of the lifted transformation is isomorphic to the lift of the section
fibre, naturally in the object. -/
private def sectionFiberUliftIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X)) :
    sectionFiber B S hS
        (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{wm, v}))
        X (ULift.up y) ≅
      sectionFiber B S hS a X y ⋙
        CategoryTheory.uliftFunctor.{wm, v} := by
  refine NatIso.ofComponents
    (fun Y => (sectionFiberUliftEquiv.{u, v, wm} B S hS a X y Y).symm.toIso) ?_
  intro Y Z f
  ext x
  change (sectionFiberUliftEquiv.{u, v, wm} B S hS a X y Z).symm
      ((sectionFiber B S hS
        (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{wm, v}))
        X (ULift.up y)).map f x) =
    (CategoryTheory.uliftFunctor.{wm, v}).map
      ((sectionFiber B S hS a X y).map f)
      ((sectionFiberUliftEquiv.{u, v, wm} B S hS a X y Y).symm x)
  apply ULift.ext
  apply Subtype.ext
  rfl

/-- Lifting the values commutes with recognizing the comparison cocone of a section fibre as
a colimit. -/
private theorem sectionFiber_ulift_isColimit_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X))
    {I : Type (max w w')} [Category.{w'} I]
    (D : I ⥤ Over X) (c : Cone D) :
    Nonempty (IsColimit ((CategoryTheory.uliftFunctor.{max w w', v}).mapCocone
      ((sectionFiber B S hS a X y).mapCocone c.op))) ↔
    Nonempty (IsColimit ((sectionFiber B S hS
      (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{max w w', v}))
      X (ULift.up y)).mapCocone c.op)) := by
  let oldFiber := sectionFiber B S hS a X y
  let newFiber := sectionFiber B S hS
    (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{max w w', v}))
    X (ULift.up y)
  let β := Functor.isoWhiskerLeft D.op
    (sectionFiberUliftIso.{u, v, max w w'} B S hS a X y)
  let cLift := (CategoryTheory.uliftFunctor.{max w w', v}).mapCocone
    (oldFiber.mapCocone c.op)
  let cNew := newFiber.mapCocone c.op
  let cPre := (Cocone.precompose β.hom).obj cLift
  let eA := (sectionFiberUliftIso.{u, v, max w w'} B S hS a X y).app
    (Opposite.op c.pt)
  let eCoc : cPre ≅ cNew := Cocone.ext eA.symm (by
    intro i
    dsimp [cPre, cLift, cNew, β, oldFiber, newFiber]
    ext x
    apply Subtype.ext
    rfl)
  have hPreIff : Nonempty (IsColimit cPre) ↔ Nonempty (IsColimit cLift) :=
    ⟨fun ⟨hc⟩ => ⟨(IsColimit.precomposeHomEquiv β cLift) hc⟩,
      fun ⟨hc⟩ => ⟨(IsColimit.precomposeHomEquiv β cLift).symm hc⟩⟩
  exact ⟨fun hc => ⟨(hPreIff.mpr hc).some.ofIsoColimit eCoc⟩,
    fun hc => hPreIff.mp ⟨hc.some.ofIsoColimit eCoc.symm⟩⟩

/-- A section fibre is limit preserving exactly when the section fibre of the lifted
transformation is, since the universe lift preserves and reflects colimits of sets. -/
private theorem sectionFiber_limitPreserving_ulift_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X)) :
    LimitPreserving.{u, v, max w w', w', u + 1, u}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a X y) ↔
    LimitPreserving.{u, max v (max w w'), max w w', w', u + 1, u}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS
        (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{max w w', v}))
        X (ULift.up y)) := by
  let U := CategoryTheory.uliftFunctor.{max w w', v}
  constructor
  · intro h I hCat hCof D c hc hAffine hAffineLimit
    rcases h I D c hc hAffine hAffineLimit with ⟨hc⟩
    exact (sectionFiber_ulift_isColimit_iff.{u, v, w, w'} B S hS a X y D c).mp
      ⟨isColimitOfPreserves U hc⟩
  · intro h I hCat hCof D c hc hAffine hAffineLimit
    rcases h I D c hc hAffine hAffineLimit with ⟨hc⟩
    exact ⟨isColimitOfReflects U
      ((sectionFiber_ulift_isColimit_iff.{u, v, w, w'} B S hS a X y D c).mpr ⟨hc⟩).some⟩

/-- A transformation is relatively limit preserving exactly when its universe lift is. -/
private theorem relativelyLimitPreserving_ulift_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) :
    RelativelyLimitPreserving.{u, v, max w w', w'} B S hS a ↔
    RelativelyLimitPreserving.{u, max v (max w w'), max w w', w'} B S hS
      (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{max w w', v})) := by
  refine ⟨?_, ?_⟩
  · intro h X y
    cases y with
    | up y =>
      exact (sectionFiber_limitPreserving_ulift_iff.{u, v, w, w'} B S hS a X y).mp
        (h X y)
  · intro h X (y : G.obj (Opposite.op X))
    exact (sectionFiber_limitPreserving_ulift_iff.{u, v, w, w'} B S hS a X y).mpr
      (h X (ULift.up y))

/-- The affine-limit criterion in the case where the value universe already contains the
indexing universe, so that no lift is needed. -/
private theorem relativelyLimitPreserving_iff_affineLimit_isPullback_ordinary
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) [UnivLE.{max w w', v}] :
    RelativelyLimitPreserving.{u, v, max w w', w'} B S hS a ↔
      ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
        (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
        IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
          IsPullback
            (colimit.desc (D.op ⋙ F) (F.mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op a))
            (a.app (Opposite.op c.pt))
            (colimit.desc (D.op ⋙ G) (G.mapCocone c.op)) := by
  constructor
  · intro hLP I inst hcof D c hc hAffine hAffineLimit
    let Q := D.op ⋙ F
    let R := D.op ⋙ G
    let h := Functor.whiskerLeft D.op a
    let cF := F.mapCocone c.op
    let cG := G.mapCocone c.op
    let dF := colimit.desc Q cF
    let dG := colimit.desc R cG
    have hComm : dF ≫ a.app (Opposite.op c.pt) = colimMap h ≫ dG := by
      apply colimit.hom_ext
      intro i
      simp [Q, R, h, cF, cG, dF, dG, ← Category.assoc, a.naturality]
    have tailLP (i : I) (yi : G.obj (Opposite.op (D.obj i))) :
        Nonempty (IsColimit
          ((sectionFiber B S hS a (D.obj i) yi).mapCocone
            (tailOverCone c i).op)) := by
      let T := tailOverFunctor D i
      let ct := tailOverCone c i
      have hct := tailOverCone_map_isLimit
        (BigFppfOver.toScheme B S hS) D c hc i
      have hAffineT : ∀ t,
          IsAffine ((Over.forget (D.obj i) ⋙
            BigFppfOver.toScheme B S hS).obj (T.obj t)) := by
        intro t
        simpa [T, tailOverFunctor] using hAffine t.left
      have hAffinePt : IsAffine ((Over.forget (D.obj i) ⋙
          BigFppfOver.toScheme B S hS).obj ct.pt) := by
        simpa [ct, tailOverCone] using hAffineLimit
      simpa [T, ct] using
        (hLP (D.obj i) yi (Over i) T ct hct hAffineT hAffinePt)
    have hι (i : Iᵒᵖ) (x : F.obj (Opposite.op (D.obj i.unop))) :
        colimit.ι R i (a.app (Opposite.op (D.obj i.unop)) x) =
          colimMap h (colimit.ι Q i x) := by
      change (a.app (Opposite.op (D.obj i.unop)) ≫ colimit.ι R i) x =
        (colimit.ι Q i ≫ colimMap h) x
      rw [ι_colimMap]
      rfl
    have hdF (i : Iᵒᵖ) (x : F.obj (Opposite.op (D.obj i.unop))) :
        dF (colimit.ι Q i x) = F.map (c.π.app i.unop).op x := by simp [dF, cF, Q]
    show IsPullback dF (colimMap h) (a.app (Opposite.op c.pt)) dG
    apply (Types.isPullback_iff dF (a.app (Opposite.op c.pt))
      (colimMap h) dG).2
    refine ⟨hComm, ?_, ?_⟩
    · intro z z' hz
      obtain ⟨i, xi, hzi⟩ := Types.jointly_surjective_of_isColimit
        (colimit.isColimit Q) z
      obtain ⟨j, xj, hzj⟩ := Types.jointly_surjective_of_isColimit
        (colimit.isColimit Q) z'
      have hG : colimit.ι R i (a.app (Opposite.op (D.obj i.unop)) xi) =
          colimit.ι R j (a.app (Opposite.op (D.obj j.unop)) xj) := by
        calc
          _ = colimMap h z := (hι i xi).trans (congrArg (fun q => colimMap h q) hzi)
          _ = colimMap h z' := hz.2
          _ = _ := (congrArg (fun q => colimMap h q) hzj.symm).trans (hι j xj).symm
      obtain ⟨k, f, g, hStage⟩ := (colimit_eq_iff (F := R)).1 hG
      let k₀ := k.unop
      let m₁ := f.unop
      let m₂ := g.unop
      let x₁ := F.map (D.map m₁).op xi
      let x₂ := F.map (D.map m₂).op xj
      have hA (i : Iᵒᵖ) (m : k₀ ⟶ i.unop)
          (x : F.obj (Opposite.op (D.obj i.unop))) :
          a.app (Opposite.op (D.obj k₀)) (F.map (D.map m).op x) =
            G.map (D.map m).op (a.app (Opposite.op (D.obj i.unop)) x) :=
        ConcreteCategory.congr_hom (a.naturality (D.map m).op) x
      have hA : a.app (Opposite.op (D.obj k₀)) x₁ =
          a.app (Opposite.op (D.obj k₀)) x₂ :=
        (hA i m₁ xi).trans (hStage.trans (hA j m₂ xj).symm)
      have hCone (i : Iᵒᵖ) (m : k₀ ⟶ i.unop)
          (x : F.obj (Opposite.op (D.obj i.unop))) :
          F.map (c.π.app k₀).op (F.map (D.map m).op x) =
            F.map (c.π.app i.unop).op x := by
        rw [← F.map_comp_apply, ← op_comp, c.w m]
      have hFapex : F.map (c.π.app k₀).op x₁ =
          F.map (c.π.app k₀).op x₂ := by
        calc
          _ = dF (colimit.ι Q i xi) := (hCone i m₁ xi).trans (hdF i xi).symm
          _ = dF z := congrArg dF hzi
          _ = dF z' := hz.1
          _ = dF (colimit.ι Q j xj) := congrArg dF hzj.symm
          _ = _ := (hdF j xj).trans (hCone j m₂ xj).symm
      let yₖ := a.app (Opposite.op (D.obj k₀)) x₁
      rcases tailLP k₀ yₖ with ⟨hP⟩
      let T := tailOverFunctor D k₀
      let ct := tailOverCone c k₀
      let P := T.op ⋙ sectionFiber B S hS a (D.obj k₀) yₖ
      let t₀ := Over.mk (𝟙 k₀)
      let p (x : F.obj (Opposite.op (D.obj k₀))) (hx : a.app (Opposite.op (D.obj k₀)) x = yₖ) :
          (sectionFiber B S hS a (D.obj k₀) yₖ).obj (Opposite.op (T.obj t₀)) := ⟨x, by
            dsimp [T, t₀, tailOverFunctor]
            rw [D.map_id, op_id, G.map_id]
            exact hx⟩
      let p₁ := p x₁ rfl
      let p₂ := p x₂ hA.symm
      let cP := (sectionFiber B S hS a (D.obj k₀) yₖ).mapCocone ct.op
      have hPapex : cP.ι.app (Opposite.op t₀) p₁ =
          cP.ι.app (Opposite.op t₀) p₂ := by
        apply Subtype.ext
        show F.map (c.π.app k₀).op x₁ = F.map (c.π.app k₀).op x₂
        exact hFapex
      let : HasColimit P := HasColimit.mk ⟨cP, hP⟩
      let eP := (colimit.isColimit P).coconePointUniqueUpToIso hP
      have he (p : P.obj (Opposite.op t₀)) :
          eP.hom (colimit.ι P (Opposite.op t₀) p) =
            cP.ι.app (Opposite.op t₀) p :=
        ConcreteCategory.congr_hom
          (IsColimit.comp_coconePointUniqueUpToIso_hom
            (colimit.isColimit P) hP (Opposite.op t₀)) p
      have hpEq : colimit.ι P (Opposite.op t₀) p₁ =
          colimit.ι P (Opposite.op t₀) p₂ := by
        have heq : eP.hom (colimit.ι P (Opposite.op t₀) p₁) =
            eP.hom (colimit.ι P (Opposite.op t₀) p₂) := by
          rw [he p₁, he p₂, hPapex]
        have h := congrArg eP.inv heq
        simpa [eP] using h
      let Q₀ := D.op ⋙ F
      let E := Over.forget k₀
      let sP : Cocone P :=
        { pt := colimit Q₀
          ι :=
            { app := fun t => TypeCat.ofHom fun q : P.obj t =>
                colimit.ι Q₀ (Opposite.op t.unop.left) q.1
              naturality := by
                intro t t' f
                ext q
                exact colimit.w_apply Q₀ (f.unop.left.op) q.1 } }
      have hglobal := congrArg (colimit.desc P sP) hpEq
      have hz (p : P.obj (Opposite.op t₀)) :
          colimit.desc P sP (colimit.ι P (Opposite.op t₀) p) =
            colimit.ι Q₀ (Opposite.op k₀) p.1 := by simp [sP, t₀]
      have hq (i : Iᵒᵖ) (m : k₀ ⟶ i.unop) (x : F.obj (Opposite.op (D.obj i.unop))) :
          colimit.ι Q₀ (Opposite.op k₀) (F.map (D.map m).op x) = colimit.ι Q i x := by
        simpa [Q₀, Q] using colimit.w_apply Q (Quiver.Hom.op m) x
      rw [hz, hz] at hglobal
      exact hzi.symm.trans ((hq i m₁ xi).symm.trans (hglobal.trans ((hq j m₂ xj).trans hzj)))
    · intro x z hx
      obtain ⟨i, yi, hzi⟩ := Types.jointly_surjective_of_isColimit
        (colimit.isColimit R) z
      have hTarget : a.app (Opposite.op c.pt) x =
          G.map (c.π.app i.unop).op yi := by
        rw [hx, ← hzi]
        simp [dG, cG, R]
      rcases tailLP i.unop yi with ⟨hP⟩
      let T := tailOverFunctor D i.unop
      let ct := tailOverCone c i.unop
      let P := T.op ⋙ sectionFiber B S hS a (D.obj i.unop) yi
      let cP := (sectionFiber B S hS a (D.obj i.unop) yi).mapCocone ct.op
      let pA : (sectionFiber B S hS a (D.obj i.unop) yi).obj
          (Opposite.op ct.pt) := ⟨x, by
            show a.app (Opposite.op c.pt) x = G.map (c.π.app i.unop).op yi
            exact hTarget⟩
      obtain ⟨t, p, hp⟩ := Types.jointly_surjective_of_isColimit hP pA
      let t₀ := t.unop
      refine ⟨colimit.ι Q (Opposite.op t₀.left) p.1, ?_, ?_⟩
      · exact (hdF (Opposite.op t₀.left) p.1).trans (congrArg Subtype.val hp)
      · have hstage : a.app (Opposite.op (D.obj t₀.left)) p.1 =
          G.map (D.map t₀.hom).op yi := p.2
        calc
          _ = colimit.ι R (Opposite.op t₀.left)
                (a.app (Opposite.op (D.obj t₀.left)) p.1) := (hι (Opposite.op t₀.left) p.1).symm
          _ = colimit.ι R (Opposite.op t₀.left)
                (G.map (D.map t₀.hom).op yi) := by simp [hstage]
          _ = colimit.ι R i yi := by
              simpa [R] using colimit.w_apply R (Quiver.Hom.op t₀.hom) yi
          _ = z := hzi
  · intro hCriterion X y I inst hcof D c hc hAffine hAffineLimit
    let D' := D ⋙ Over.forget X
    let c' := (Over.forget X).mapCone c
    have hLimit' : IsLimit
        ((BigFppfOver.toScheme B S hS).mapCone c') :=
      IsLimit.ofIsoLimit hc (Functor.mapConeMapCone c).symm
    have hSq := hCriterion I D' c' hLimit' hAffine hAffineLimit
    exact sectionFiber_colimit_isColimit_of_isPullback B S hS a X y D c hSq

/-- The affine-limit comparison square characterizes relative limit
preservation of a transformation of presheaves. -/
@[stacks 06BC]
public theorem relativelyLimitPreserving_iff_affineLimit_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) :
    RelativelyLimitPreserving.{u, v, max w w', w'} B S hS a ↔
      ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
        (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
        IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
          let U := CategoryTheory.uliftFunctor.{max w w', v}
          let F' := F ⋙ U
          let G' := G ⋙ U
          IsPullback
            (colimit.desc (D.op ⋙ F') (F'.mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight a U)))
            (U.map (a.app (Opposite.op c.pt)))
            (colimit.desc (D.op ⋙ G') (G'.mapCocone c.op)) := by
  let : UnivLE.{max w w', max v (max w w')} := inferInstance
  simpa only [Functor.whiskerRight_app] using
    (relativelyLimitPreserving_ulift_iff B S hS a).trans
      (relativelyLimitPreserving_iff_affineLimit_isPullback_ordinary.{u,
        max v (max w w'), max w w', w'} B S hS
          (Functor.whiskerRight a (CategoryTheory.uliftFunctor.{max w w', v})))

end AlgebraicGeometry
