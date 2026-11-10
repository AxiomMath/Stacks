module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ClosedFibreFlatteningSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkFinitePresentation

/-!
# A finitely presented flattening subscheme along the closed fibre

Let `A` be a henselian local ring, let `f : X ⟶ Spec A` be locally of finite type and locally of
finite presentation, let `F` be a finite type finitely presented quasi-coherent `O_X`-module and
let `E` be a closed quasi-compact subset of the fibre of `f` over the closed point. Then the
closed subscheme of `Spec A` detecting flatness along `E` after every pointed base change can be
chosen of finite presentation.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_closedSubscheme_flatOverAt_iff_factors`:
  **Stacks Tag 05PI**, the finite-presentation refinement.

## Implementation notes

For each point `x` of `E` the pointwise statement
`AlgebraicGeometry.exists_finitePresentation_closedSubscheme_flatOverAt_iff_factorStalk`,
**Stacks Tag 05PH**, gives a finitely presented closed subscheme `Z_x`; its pointwise
hypotheses hold because `f` is locally of finite presentation
(`AlgebraicGeometry.Scheme.Hom.finitePresentation_appLE`) and
because the stalk of a finitely presented module is finitely presented
(`Stacks.SheafOfModules.finitePresentation_stalk`). The locus of points of `X` all of whose
preimages in `X ×_{Spec A} Z_x` are flat is open
(`AlgebraicGeometry.isOpen_setOf_isFlatOverAt_modulePullback` together with the fact that the
first projection of a base change along a closed immersion is closed), and contains `x`; since
`E` is quasi-compact, finitely many of these opens cover the image of `E`. The intersection of
the `Z_x` over those finitely many points already has the universal property asked of all of
`E`, because the ideal sheaf of `Z_z` is below that of `Z_x` — so `Z_x` is contained in `Z_z` —
whenever `z` lies in the open attached to `x`. A finite intersection of finitely presented
closed subschemes is finitely presented by
`Stacks.Flatness.finitePresentation_subschemeι_sup`.

## References

* [Stacks Project, Tag 05PI](https://stacks.math.columbia.edu/tag/05PI)
* [Stacks Project, Tag 05PH](https://stacks.math.columbia.edu/tag/05PH)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite intersection of closed subschemes of finite presentation is of finite
presentation. -/
private theorem finitePresentation_subscheme_finsetSup {S : Scheme.{u}}
    {ι : Type*} (J : ι → S.IdealSheafData) (a : Finset ι)
    (hJ : ∀ i ∈ a, FinitePresentation (J i).subschemeι) :
    FinitePresentation (a.sup J).subschemeι := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact Stacks.Flatness.finitePresentation_subschemeι_bot
  | @insert i a hi ih =>
    rw [Finset.sup_insert]
    exact Stacks.Flatness.finitePresentation_subschemeι_sup
      (hJ i (Finset.mem_insert_self ..))
      (ih fun j hj => hJ j (Finset.mem_insert_of_mem hj))

/-- The set of points of `X` above which the pullback of `F` to the base change along a closed
immersion is flat is open. -/
private theorem isOpen_forall_flatOverAt_above {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (I : S.IdealSheafData) :
    IsOpen {x : X | ∀ y : (pullback f I.subschemeι : Scheme.{u}),
      pullback.fst f I.subschemeι y = x →
      AlgebraicGeometry.IsFlatOverAt (pullback.snd f I.subschemeι).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f I.subschemeι)).obj F) y} := by
  classical
  have hopen : IsOpen {y : (pullback f I.subschemeι : Scheme.{u}) |
      AlgebraicGeometry.IsFlatOverAt (pullback.snd f I.subschemeι).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f I.subschemeι)).obj F) y} :=
    @AlgebraicGeometry.isOpen_setOf_isFlatOverAt_modulePullback _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback f I.subschemeι) F ‹F.IsQuasicoherent›
      ‹F.IsFinitePresentation› inferInstance
  convert ((pullback.fst f I.subschemeι).isClosedEmbedding.isClosedMap _
    hopen.isClosed_compl).isOpen_compl using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image]
  exact ⟨fun h ⟨y, hy, hxy⟩ => hy (h y hxy), fun h y hy => by_contra fun hn => h ⟨y, hn, hy⟩⟩

/-- The canonical morphism from the spectrum of the stalk at the closed point of the spectrum of
a local ring is an isomorphism. -/
private theorem isIso_fromSpecStalk_closedPoint (R : CommRingCat.{u}) [IsLocalRing R] :
    IsIso ((Spec R).fromSpecStalk (IsLocalRing.closedPoint R)) := by
  rw [← Spec_stalkClosedPointIso R]
  infer_instance

/-- A nonempty closed subscheme of the spectrum of a local ring has a point over the closed
point at which the canonical morphism from the spectrum of the local ring is an
isomorphism. -/
private theorem exists_closedPoint_iso_stalk {A : Type u} [CommRing A] [IsLocalRing A]
    {T : Scheme.{u}} (i : T ⟶ Spec (.of A)) [IsClosedImmersion i] [Nonempty T] :
    ∃ t : T, i t = IsLocalRing.closedPoint A ∧ IsIso (T.fromSpecStalk t) := by
  have : IsAffine T := isAffine_of_isAffineHom i
  have : Nonempty (⊤ : T.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let φ : CommRingCat.of A ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (.of A)).inv ≫ i.appTop
  have hφ : Function.Surjective φ :=
    (i.app_surjective ⊤ (isAffineOpen_top _)).comp
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective
  have : IsLocalRing Γ(T, ⊤) := IsLocalRing.of_surjective' φ.hom hφ
  have : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hφ
  let p : Spec Γ(T, ⊤) := IsLocalRing.closedPoint Γ(T, ⊤)
  let t : T := T.isoSpec.inv p
  refine ⟨t, ?_, ?_⟩
  · change (T.isoSpec.inv ≫ i) p = _
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    exact AlgebraicGeometry.Spec_closedPoint (f := φ)
  · have := isIso_fromSpecStalk_closedPoint Γ(T, ⊤)
    have : IsIso (Spec.map (T.isoSpec.inv.stalkMap p) ≫ T.fromSpecStalk t) := by
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk T.isoSpec.inv (x := p)]
      infer_instance
    exact IsIso.of_isIso_comp_left (Spec.map (T.isoSpec.inv.stalkMap p)) _

/-- If `Spec O_{Z, t} ⟶ S` factors through a closed subscheme `I` for every point `t` of a
closed subscheme `J` over the closed point, then `I` contains `J`. -/
private theorem le_of_pointed_stalk_factors {A : Type u} [CommRing A] [IsLocalRing A]
    (I J : (Spec (.of A)).IdealSheafData)
    (H : ∀ t : J.subscheme, J.subschemeι t = IsLocalRing.closedPoint A →
      ∃ h : Spec (J.subscheme.presheaf.stalk t) ⟶ I.subscheme,
        h ≫ I.subschemeι = J.subscheme.fromSpecStalk t ≫ J.subschemeι) : I ≤ J := by
  cases isEmpty_or_nonempty J.subscheme with
  | inl h =>
    have : J = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      exact SetLike.coe_injective <| J.range_subschemeι.symm.trans (Set.range_eq_empty_iff.mpr h)
    simp [this]
  | inr h =>
    obtain ⟨t, ht, h_iso⟩ := exists_closedPoint_iso_stalk J.subschemeι
    obtain ⟨a, ha⟩ := H t ht
    have hle := Scheme.Hom.le_ker_comp a I.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι, ha,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι] at hle

/-- **Stacks Project, Tag 05PI.** When the morphism and the module are in addition locally of
finite presentation and the chosen subset of the closed fibre is closed and quasi-compact, the
closed subscheme of the henselian local base detecting flatness along that subset can be chosen
of finite presentation. -/
@[stacks 05PI "finite-presentation refinement"]
theorem exists_finitePresentation_closedSubscheme_flatOverAt_iff_factors
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [F.IsFinitePresentation]
    (E : Set (f.fiber (IsLocalRing.closedPoint A)))
    (_ : IsClosed E) (hEcompact : IsCompact E) :
    ∃ I : (Spec (.of A)).IdealSheafData,
      FinitePresentation I.subschemeι ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)) (t : T)
        (_ : g t = IsLocalRing.closedPoint A),
        (∀ y : (pullback f g : Scheme.{u}),
          (pullback.snd f g) y = t →
          (pullback.fst f g) y ∈
            (f.fiberι (IsLocalRing.closedPoint A)) '' E →
          AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
            ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
        ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
          h ≫ I.subschemeι = T.fromSpecStalk t ≫ g := by
  classical
  let s : Spec (.of A) := IsLocalRing.closedPoint A
  have := isIso_fromSpecStalk_closedPoint (.of A)
  have : HenselianLocalRing ((Spec (.of A)).presheaf.stalk s) :=
    henselianLocalRing_stalk_closedPoint A
  have hfp (x : X) : FinitePresentationAt f x := by
    let V : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
        isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))⟩
    exact ⟨⟨⊤, isAffineOpen_top _⟩, V, X.affineCover.covers x, by simp,
      f.finitePresentation_appLE (isAffineOpen_top _) V.2 _⟩
  have H (z : E) :=
    exists_finitePresentation_closedSubscheme_flatOverAt_iff_factorStalk
      f F (f.fiberι s z) s (f.apply_fiberι s z) (hfp _)
      (@Stacks.SheafOfModules.finitePresentation_stalk _ F ‹F.IsFinitePresentation› _)
  choose J hJfp hJ using H
  let U (z : E) : Set X := {w | ∀ y : (pullback f (J z).subschemeι : Scheme.{u}),
    pullback.fst f (J z).subschemeι y = w →
    AlgebraicGeometry.IsFlatOverAt (pullback.snd f (J z).subschemeι).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f (J z).subschemeι)).obj F) y}
  have hUopen (z : E) : IsOpen (U z) := isOpen_forall_flatOverAt_above f F (J z)
  have hzU (z : E) : f.fiberι s z ∈ U z := by
    intro y hy
    have ht : (J z).subschemeι (pullback.snd f (J z).subschemeι y) = s := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hy]
      exact f.apply_fiberι s z
    exact (hJ z (J z).subschemeι _ ht).mpr
      ⟨(J z).subscheme.fromSpecStalk _, rfl⟩ y rfl hy
  have hle (z w : E) (hw : f.fiberι s w ∈ U z) : J w ≤ J z :=
    le_of_pointed_stalk_factors _ _ fun t ht =>
      (hJ w (J z).subschemeι t ht).mp fun y _ hy => hw y hy
  obtain ⟨a, ha⟩ := (hEcompact.image (f.fiberι s).continuous).elim_finite_subcover
    U hUopen (by
      rintro _ ⟨z, hz, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩)
  let I := a.sup J
  have hJI (w : E) : J w ≤ I := by
    obtain ⟨z, hz, hw⟩ := Set.mem_iUnion₂.mp (ha (Set.mem_image_of_mem _ w.2))
    exact (hle z w hw).trans (Finset.le_sup hz)
  refine ⟨I, finitePresentation_subscheme_finsetSup J a fun z _ => hJfp z, fun T g t ht => ?_⟩
  have key (z : E) := (hJ z g t ht).trans (factorsThrough_ideal_iff_ideal_le_ker (J z) _)
  rw [factorsThrough_ideal_iff_ideal_le_ker]
  exact ⟨fun hflat => Finset.sup_le fun z _ =>
      (key z).mp fun y hy hzy => hflat y hy ⟨_, z.2, hzy.symm⟩,
    fun h y hy ⟨w, hw, hwy⟩ => (key ⟨w, hw⟩).mpr ((hJI ⟨w, hw⟩).trans h) y hy hwy.symm⟩

end AlgebraicGeometry

end
