module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# The flatness functor is limit preserving

Let `f : X ⟶ S` be a quasi-compact morphism of schemes which is locally of finite presentation
and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. Then the flatness functor
of `F` is locally of finite presentation in the sense of `AlgebraicGeometry.LimitPreserving`: it
carries a cofiltered inverse limit of affine schemes over `S` to a filtered colimit of sets.

The functor is subterminal, so the colimit statement reduces to a single assertion: if the
base-changed module is flat over the limit, then it is already flat over one of the stages.
That is proved by reducing to an affine situation. Over an affine stage `T` the fibre product
`X ×_S T` is quasi-compact, so it is covered by finitely many affine opens whose disjoint union
`X' ⟶ X ×_S T` is flat, surjective and of finite presentation over `T`. Flatness of the
base-changed module over a scheme over `T` may therefore be tested after pulling back to `X'`,
and there the approximation result for flatness along a cofiltered limit applies.

## Main results

* `AlgebraicGeometry.FlatnessSituation.flatFunctor_limitPreserving`: the flatness functor of a
  finitely presented quasi-coherent module along a quasi-compact, locally finitely presented
  morphism is limit preserving.

## Implementation notes

The object and morphism universes of the index category of the tested inverse system are
independent of each other and of the universe of the schemes; the scheme universe is the
maximum of those two and a third parameter, so the schemes may live in a strictly larger
universe than the index category.

Two comparisons are isolated as private lemmas and used in both directions: the identification
of `X ×_S T'` with `(X ×_S T) ×_T T'` for a morphism `T' ⟶ T` over `S`, which is
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`; and the comparison of flatness over a scheme
over `T` before and after pulling back along a flat surjective morphism of schemes over `T`. The
invariance of flatness over the base under postcomposing with an isomorphism is
`AlgebraicGeometry.isFlatOver_overPullback_map_iff` and its two helpers, in
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness`.

## References

* [Stacks Project, Tag 05MY](https://stacks.math.columbia.edu/tag/05MY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u v w

namespace AlgebraicGeometry.FlatnessSituation

/-- A quasi-compact scheme is the target of a flat surjective morphism, locally of finite
presentation, from an affine scheme. -/
private theorem exists_isAffine_flat_surjective_locallyOfFinitePresentation (Y : Scheme.{u})
    [CompactSpace Y] : ∃ (X' : Scheme.{u}) (q : X' ⟶ Y), IsAffine X' ∧ Flat q ∧ Surjective q ∧
      LocallyOfFinitePresentation q := by
  let 𝒞 := Y.affineCover.finiteSubcover
  have _ : Finite 𝒞.I₀ := by
    dsimp only [𝒞]
    infer_instance
  have _ (k : 𝒞.I₀) : IsAffine (𝒞.X k) := by
    dsimp only [𝒞]
    infer_instance
  have _ (k : 𝒞.I₀) : LocallyOfFinitePresentation (𝒞.f k) := by
    dsimp only [𝒞]
    infer_instance
  have _ : IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
  let q : (∐ 𝒞.X) ⟶ Y := Sigma.desc 𝒞.f
  have _ : Flat q := by
    dsimp only [q]
    infer_instance
  have _ : Surjective q := by
    dsimp only [q]
    infer_instance
  exact ⟨∐ 𝒞.X, q, inferInstance, inferInstance, inferInstance,
    IsZariskiLocalAtSource.sigmaDesc fun k ↦ inferInstance⟩

/-- For a commuting square of morphisms of schemes, the two ways of pulling a module on the
target of the square back to its source agree. -/
private noncomputable def modulePullbackSquareIso {A B C E : Scheme.{u}}
    (a : A ⟶ B) (b : C ⟶ A) (c : E ⟶ B) (d : C ⟶ E) (h : b ≫ a = d ≫ c)
    (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)) :
    (modulePullback b.toLRSHom.toShHom).obj ((modulePullback a.toLRSHom.toShHom).obj M) ≅
      (modulePullback d.toLRSHom.toShHom).obj ((modulePullback c.toLRSHom.toShHom).obj M) :=
  have eMid : (modulePullback (b ≫ a).toLRSHom.toShHom).obj M ≅
      (modulePullback (d ≫ c).toLRSHom.toShHom).obj M := by rw [h]
  ((schemeModulePullbackCompIso b a).app M).trans
    (eMid.trans ((schemeModulePullbackCompIso d c).app M).symm)


/-- Pulling a module back along `b` and then along `a` is pulling it back along `a ≫ b`, which
may be given as any morphism `c` equal to it. -/
private noncomputable def modulePullbackCompIsoOfEq {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (M : SheafOfModules.{u} (structureSheafRing C.toRingedSpace)) :
    (modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M) ≅
      (modulePullback c.toLRSHom.toShHom).obj M :=
  ((schemeModulePullbackCompIso a b).app M).trans (by rw [h])

/-- Flatness over the base transfers along an isomorphism of the source: if a quasi-coherent
module on `X'` is flat over `S` and `e : X ≅ X'` is an isomorphism over `S`, then the pullback
of the module to `X` is flat over `S`. -/
private theorem isFlatOver_pullback_of_iso {X X' S : Scheme.{u}} (e : X ≅ X') (f : X ⟶ S)
    (g : X' ⟶ S) (he : e.hom ≫ g = f)
    (M : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) [M.IsQuasicoherent]
    (hM : IsFlatOver g.toLRSHom.toShHom M) :
    IsFlatOver f.toLRSHom.toShHom ((modulePullback e.hom.toLRSHom.toShHom).obj M) :=
  have hsq : IsPullback e.hom f g (𝟙 S) :=
    IsPullback.of_horiz_isIso (CommSq.mk (by simpa using he))
  modulePullback_isFlatOver hsq M hM

/-- Flatness over a scheme `U` over `T` of the pullback of a quasi-coherent module on a scheme
`X` over `T` is detected after a further pullback along a flat surjective morphism
`q : X' ⟶ X`. -/
private theorem isFlatOver_pullback_comp_iff {T X X' U : Scheme.{u}} (p : X ⟶ T) (q : X' ⟶ X)
    [Flat q] [Surjective q] (b : U ⟶ T)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [M.IsQuasicoherent] :
    IsFlatOver (pullback.snd (q ≫ p) b).toLRSHom.toShHom
        ((modulePullback (pullback.fst (q ≫ p) b).toLRSHom.toShHom).obj
          ((modulePullback q.toLRSHom.toShHom).obj M)) ↔
      IsFlatOver (pullback.snd p b).toLRSHom.toShHom
        ((modulePullback (pullback.fst p b).toLRSHom.toShHom).obj M) := by
  set z₁ := pullback.fst p b
  set z₂ := pullback.snd p b
  set w₁ := pullback.fst z₁ q
  set w₂ := pullback.snd z₁ q
  have hw : w₂ ≫ q = w₁ ≫ z₁ := pullback.condition.symm
  have _ : Flat w₁ := by dsimp only [w₁]; infer_instance
  have _ : Surjective w₁ := by dsimp only [w₁]; infer_instance
  have _ : ((modulePullback q.toLRSHom.toShHom).obj M).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent q.toLRSHom.toShHom M
  have _ : ((modulePullback z₁.toLRSHom.toShHom).obj M).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent z₁.toLRSHom.toShHom M
  have _ : ((modulePullback w₂.toLRSHom.toShHom).obj
      ((modulePullback q.toLRSHom.toShHom).obj M)).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent w₂.toLRSHom.toShHom _
  have _ : ((modulePullback (pullback.fst (q ≫ p) b).toLRSHom.toShHom).obj
      ((modulePullback q.toLRSHom.toShHom).obj M)).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent _ _
  have eSquare := (modulePullbackCompIsoOfEq w₂ q _ rfl M).trans
    (modulePullbackCompIsoOfEq w₁ z₁ _ hw.symm M).symm
  have hcover : IsPullback (w₁ ≫ z₂) w₂ b (q ≫ p) := by
    convert (IsPullback.of_hasPullback z₁ q).paste_horiz (IsPullback.of_hasPullback p b).flip
      using 1
  have eCoverHom := modulePullbackCompIsoOfEq hcover.flip.isoPullback.hom
    (pullback.fst (q ≫ p) b) w₂ hcover.flip.isoPullback_hom_fst
    ((modulePullback q.toLRSHom.toShHom).obj M)
  have eCoverInv := modulePullbackCompIsoOfEq hcover.flip.isoPullback.inv w₂
    (pullback.fst (q ≫ p) b) hcover.flip.isoPullback_inv_fst
    ((modulePullback q.toLRSHom.toShHom).obj M)
  exact ⟨fun hflat ↦ (isFlatOver_iff_modulePullback_isFlatOver w₁ z₂
      ((modulePullback z₁.toLRSHom.toShHom).obj M)).mpr
      (isFlatOver_of_moduleIso (w₁ ≫ z₂).toLRSHom.toShHom eSquare
        (isFlatOver_of_moduleIso (w₁ ≫ z₂).toLRSHom.toShHom eCoverHom
          (isFlatOver_pullback_of_iso hcover.flip.isoPullback (w₁ ≫ z₂)
            (pullback.snd (q ≫ p) b) hcover.flip.isoPullback_hom_snd _ hflat))),
    fun hflat ↦ isFlatOver_of_moduleIso (pullback.snd (q ≫ p) b).toLRSHom.toShHom eCoverInv
      (isFlatOver_pullback_of_iso hcover.flip.isoPullback.symm
        (pullback.snd (q ≫ p) b) (w₁ ≫ z₂) hcover.flip.isoPullback_inv_snd _
        (isFlatOver_of_moduleIso (w₁ ≫ z₂).toLRSHom.toShHom eSquare.symm
          ((isFlatOver_iff_modulePullback_isFlatOver w₁ z₂
            ((modulePullback z₁.toLRSHom.toShHom).obj M)).mp hflat)))⟩

/-- Flatness over `T'` of the module pulled back to `X ×_S T'` is flatness over `T'` of the
module pulled back to `(X ×_S T) ×_T T'`, for a morphism `T' ⟶ T` of schemes over `S`. -/
private theorem isFlatOver_pullbackAssoc_iff {X S T T' : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
    (g : T' ⟶ T) (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsFlatOver (pullback.snd f (g ≫ t)).toLRSHom.toShHom
        ((modulePullback (pullback.fst f (g ≫ t)).toLRSHom.toShHom).obj F) ↔
      IsFlatOver (pullback.snd (pullback.snd f t) g).toLRSHom.toShHom
        ((modulePullback (pullback.fst (pullback.snd f t) g).toLRSHom.toShHom).obj
          ((modulePullback (pullback.fst f t).toLRSHom.toShHom).obj F)) := by
  set p₁ := pullback.fst f t
  set p₂ := pullback.snd f t
  set q₁ := pullback.fst p₂ g
  set q₂ := pullback.snd p₂ g
  set r₁ := pullback.fst f (g ≫ t)
  set r₂ := pullback.snd f (g ≫ t)
  have _ : ((modulePullback r₁.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent r₁.toLRSHom.toShHom F
  have _ : ((modulePullback p₁.toLRSHom.toShHom).obj F).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent p₁.toLRSHom.toShHom F
  have _ : ((modulePullback q₁.toLRSHom.toShHom).obj
      ((modulePullback p₁.toLRSHom.toShHom).obj F)).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent q₁.toLRSHom.toShHom _
  set α := pullbackLeftPullbackSndIso f t g
  have hsnd : α.hom ≫ r₂ = q₂ := pullbackLeftPullbackSndIso_hom_snd f t g
  have hfst : α.hom ≫ r₁ = q₁ ≫ p₁ := pullbackLeftPullbackSndIso_hom_fst f t g
  have hinvfst : α.inv ≫ q₁ ≫ p₁ = r₁ := pullbackLeftPullbackSndIso_inv_fst f t g
  have eComp := modulePullbackCompIsoOfEq q₁ p₁ _ rfl F
  have eAlpha := modulePullbackCompIsoOfEq α.hom r₁ (q₁ ≫ p₁) hfst F
  have eAlphaInv := modulePullbackCompIsoOfEq α.inv (q₁ ≫ p₁) r₁ hinvfst F
  have hinvsnd : α.inv ≫ q₂ = r₂ := by rw [← hsnd, Iso.inv_hom_id_assoc]
  exact ⟨fun hflat ↦ isFlatOver_of_moduleIso q₂.toLRSHom.toShHom (eAlpha.trans eComp.symm)
      (isFlatOver_pullback_of_iso α q₂ r₂ hsnd _ hflat),
    fun hflat ↦ isFlatOver_of_moduleIso r₂.toLRSHom.toShHom
      (((modulePullback α.inv.toLRSHom.toShHom).mapIso eComp).trans eAlphaInv)
      (isFlatOver_pullback_of_iso α.symm r₂ q₂ hinvsnd _ hflat)⟩

/-- Flatness over `U` of the base change of `F` along `U ⟶ T ⟶ S` is flatness over `U` of its
further pullback along a flat surjective `q : X' ⟶ X ×_S T`, in the form used by the
approximation of flatness along a cofiltered limit. -/
private theorem isFlatOver_overPullback_cover_iff {X S T X' U : Scheme.{u}} (f : X ⟶ S)
    (t : T ⟶ S) (q : X' ⟶ pullback f t) [Flat q] [Surjective q] (b : U ⟶ T)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    IsFlatOver ((Over.pullback b).map (Over.homMk (Over.mk (q ≫ pullback.snd f t)).hom :
          Over.mk (q ≫ pullback.snd f t) ⟶ Over.mk (𝟙 T))).left.toLRSHom.toShHom
        ((modulePullback (pullback.fst (q ≫ pullback.snd f t) b).toLRSHom.toShHom).obj
          ((modulePullback q.toLRSHom.toShHom).obj
            ((modulePullback (pullback.fst f t).toLRSHom.toShHom).obj F))) ↔
      IsFlatOver (pullback.snd f (b ≫ t)).toLRSHom.toShHom
        ((modulePullback (pullback.fst f (b ≫ t)).toLRSHom.toShHom).obj F) := by
  have _ := SheafOfModules.modulePullback_isQuasicoherent (pullback.fst f t).toLRSHom.toShHom F
  exact (isFlatOver_overPullback_map_iff _ b _).trans
    ((isFlatOver_pullback_comp_iff (pullback.snd f t) q b _).trans
      (isFlatOver_pullbackAssoc_iff f t b F).symm)

/-- If the base change to the limit of a cofiltered system of affine schemes over the base is
flat, then so is the base change to some stage of the system. -/
private theorem exists_isFlatAfterBaseChange_of_isLimit (D : FlatnessSituation.{max u v w})
    [QuasiCompact D.f] [LocallyOfFinitePresentation D.f] [D.F.IsFinitePresentation]
    {I : Type v} [Category.{w} I] [IsCofiltered I] (E : I ⥤ Over D.S) (c : Cone E)
    (hc : IsLimit ((Over.forget D.S).mapCone c)) (hE : ∀ k, IsAffine (E.obj k).left)
    (h : D.IsFlatAfterBaseChange c.pt) : ∃ j, D.IsFlatAfterBaseChange (E.obj j) := by
  let Syst : I ⥤ Scheme.{max u v w} := E ⋙ Over.forget D.S
  let cS : Cone Syst := (Over.forget D.S).mapCone c
  have hcS : IsLimit cS := hc
  have _ : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.choice (IsCofiltered.nonempty : Nonempty I)
  have _ (k : I) : IsAffine (Syst.obj k) := hE k
  have _ (k : I) : CompactSpace (Syst.obj k) := Scheme.compactSpace_of_isAffine (Syst.obj k)
  have _ (k : I) : QuasiSeparatedSpace (Syst.obj k) := by infer_instance
  have _ {k l : I} (a : k ⟶ l) : IsAffineHom (Syst.map a) := isAffineHom_of_isAffine (Syst.map a)
  have _ : IsAffine (E.obj i).left := hE i
  have _ : CompactSpace (pullback D.f (E.obj i).hom : Scheme.{max u v w}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd D.f (E.obj i).hom)
  obtain ⟨X', q, _, _, _, _⟩ :=
    exists_isAffine_flat_surjective_locallyOfFinitePresentation (pullback D.f (E.obj i).hom)
  have _ : CompactSpace X' := Scheme.compactSpace_of_isAffine X'
  let X : Over (E.obj i).left := Over.mk (q ≫ pullback.snd D.f (E.obj i).hom)
  let Y : Over (E.obj i).left := Over.mk (𝟙 (E.obj i).left)
  let fXY : X ⟶ Y := Over.homMk X.hom
  have _ : (D.baseChangeModule (E.obj i)).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent _ D.F
  have _ : (D.baseChangeModule (E.obj i)).IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation _ D.F
  let M' := (modulePullback q.toLRSHom.toShHom).obj (D.baseChangeModule (E.obj i))
  have _ : M'.IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent q.toLRSHom.toShHom _
  have _ : M'.IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation q.toLRSHom.toShHom _
  have hXfp : FinitePresentation X.hom :=
    FinitePresentation.mk (f := q ≫ pullback.snd D.f (E.obj i).hom)
      inferInstance inferInstance inferInstance
  have hYfp : FinitePresentation Y.hom :=
    FinitePresentation.mk (f := 𝟙 (E.obj i).left) inferInstance inferInstance inferInstance
  have hlimit : IsFlatOver
      (pullback.snd D.f (cS.π.app i ≫ (E.obj i).hom)).toLRSHom.toShHom
      ((modulePullback
        (pullback.fst D.f (cS.π.app i ≫ (E.obj i).hom)).toLRSHom.toShHom).obj D.F) := by
    rw [show cS.π.app i ≫ (E.obj i).hom = c.pt.hom from (c.π.app i).w]
    exact h
  obtain ⟨j, e, hstage⟩ := eventually_isFlatOver_modulePullback Syst cS hcS i X Y hXfp hYfp
    fXY M' ((isFlatOver_overPullback_cover_iff D.f (E.obj i).hom q (cS.π.app i) D.F).2 hlimit)
  have hback := (isFlatOver_overPullback_cover_iff D.f (E.obj i).hom q (Syst.map e) D.F).1 hstage
  rw [show Syst.map e ≫ (E.obj i).hom = (E.obj j).hom from (E.map e).w] at hback
  exact ⟨j, hback⟩

/-- **Stacks Project, Tag 05MY.** Part (2): for a quasi-compact morphism which is locally of
finite presentation and a quasi-coherent module of finite presentation, the flatness functor is
limit preserving: it carries a cofiltered inverse limit of affine schemes over the base to a
filtered colimit of sets. -/
@[stacks 05MY "flat_functor_limit_preserving"]
public theorem flatFunctor_limitPreserving (D : FlatnessSituation.{max u v w})
    [QuasiCompact D.f] [LocallyOfFinitePresentation D.f] [D.F.IsFinitePresentation] :
    LimitPreserving.{max u v w, 0, v, w, max u v w + 1, max u v w}
      (Over.forget D.S) D.flatFunctor := by
  intro I _ _ E c hc hE _
  refine ⟨Types.FilteredColimit.isColimitOf (E.op ⋙ D.flatFunctor)
    (D.flatFunctor.mapCocone c.op) (fun y ↦ ?_) fun k l xk xl _ ↦ ?_⟩
  · obtain ⟨j, hj⟩ :=
      exists_isFlatAfterBaseChange_of_isLimit.{u, max v w, w} D E c hc hE y.down
    exact ⟨Opposite.op j, ⟨hj⟩, @Subsingleton.elim _ (D.flatFunctor_obj_subsingleton _) _ _⟩
  · obtain ⟨m, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs k l
    exact ⟨m, a, b, @Subsingleton.elim _ (D.flatFunctor_obj_subsingleton _) _ _⟩

end AlgebraicGeometry.FlatnessSituation
