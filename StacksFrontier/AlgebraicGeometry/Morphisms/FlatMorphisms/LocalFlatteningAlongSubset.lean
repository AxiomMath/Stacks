module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Henselian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.LocalFlatteningAtPoint
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ClosedFibreFlatteningSubscheme
import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
import StacksFrontier.Topology.Sheaves.RingedSpace.StalkFinitePresentation

/-!
# The local flattening subscheme along a subset of the closed fibre

Let `A` be a henselian local ring, `f : X ⟶ Spec A` locally of finite type, `F` a quasi-coherent
`𝒪_X`-module of finite type and `E` a set of points of `X` over the closed point. The closed
subschemes of the points of `E` (Stacks 05PH) have an intersection `Z` which detects, after every
pointed base change `(T, t) ⟶ (Spec A, s)`, flatness of `F_T` over `T` at the points of `X_T` above
`t` mapping into `E`. If `f` is locally of finite presentation, `F` of finite presentation and `E`
quasi-compact, finitely many of these closed subschemes suffice, by openness of the flat locus, and
`Z` is of finite presentation. This is the scheme case of the flattening in the local case,
Stacks 05PI, and the input of Stacks 0CWP.

## Main definitions

* `AlgebraicGeometry.LocalFlattening.FlatAlongAfter`: flatness of the base change along `E`.

## Main results

* `AlgebraicGeometry.LocalFlattening.exists_idealSheafData_flatAlongAfter_iff`
* `AlgebraicGeometry.LocalFlattening.exists_finitePresentation_idealSheafData_flatAlongAfter_iff`
* `AlgebraicGeometry.LocalFlattening.flatAlongAfter_iff_of_isPullback`: the condition may be read
  on any cartesian square.

## References

* [Stacks Project, Tag 05PI](https://stacks.math.columbia.edu/tag/05PI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.LocalFlattening

private alias henselian_stalk_of_spec_local :=
  AlgebraicGeometry.henselianLocalRing_stalk_closedPoint

/-- The canonical map from the spectrum of the stalk at the closed point of `Spec R` is an
isomorphism. -/
private theorem isIso_fromSpecStalk_closedPoint (R : CommRingCat.{u}) [IsLocalRing R] :
    IsIso ((Spec R).fromSpecStalk (IsLocalRing.closedPoint R)) := by
  rw [← AlgebraicGeometry.Spec_stalkClosedPointIso R]
  infer_instance

/-- A morphism factors through the closed subscheme cut out by an ideal sheaf exactly when the
ideal sheaf is contained in its kernel. -/
theorem exists_comp_subschemeι_eq_iff_le_ker {S T : Scheme.{u}} (I : S.IdealSheafData)
    (q : T ⟶ S) :
    (∃ h : T ⟶ I.subscheme, h ≫ I.subschemeι = q) ↔ I ≤ q.ker := by
  constructor
  · rintro ⟨h, rfl⟩
    simpa using Scheme.Hom.le_ker_comp h I.subschemeι
  · intro h
    exact ⟨q.toImage ≫ Scheme.IdealSheafData.inclusion h, by simp⟩

private theorem isPullback_subscheme_sup {S : Scheme.{u}} (I J : S.IdealSheafData) :
    IsPullback (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      I.subschemeι J.subschemeι := by
  let a := Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J)
  let b := Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J)
  have hab : a ≫ I.subschemeι = b ≫ J.subschemeι := by simp [a, b]
  apply IsPullback.of_isLimit (c := PullbackCone.mk a b hab)
  apply PullbackCone.isLimitAux'
  intro c
  have hI : I ≤ (c.fst ≫ I.subschemeι).ker :=
    (exists_comp_subschemeι_eq_iff_le_ker I _).mp ⟨c.fst, rfl⟩
  have hJ : J ≤ (c.fst ≫ I.subschemeι).ker :=
    (exists_comp_subschemeι_eq_iff_le_ker J _).mp ⟨c.snd, c.condition.symm⟩
  let l := (c.fst ≫ I.subschemeι).toImage ≫
    Scheme.IdealSheafData.inclusion (sup_le hI hJ)
  have hl : l ≫ (I ⊔ J).subschemeι = c.fst ≫ I.subschemeι := by simp [l]
  have hla : l ≫ a = c.fst := (cancel_mono I.subschemeι).mp (by simpa [a] using hl)
  have hlb : l ≫ b = c.snd :=
    (cancel_mono J.subschemeι).mp (by simpa [b] using hl.trans c.condition)
  exact ⟨l, hla, hlb, fun hm _ => (cancel_mono a).mp (hm.trans hla.symm)⟩

private theorem finitePresentation_subscheme_sup {S : Scheme.{u}}
    (I J : S.IdealSheafData)
    (hI : AlgebraicGeometry.FinitePresentation I.subschemeι)
    (hJ : AlgebraicGeometry.FinitePresentation J.subschemeι) :
    AlgebraicGeometry.FinitePresentation (I ⊔ J).subschemeι := by
  have : LocallyOfFinitePresentation I.subschemeι := hI.1
  have : LocallyOfFinitePresentation J.subschemeι := hJ.1
  let a := Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J)
  have : LocallyOfFinitePresentation a :=
    MorphismProperty.of_isPullback (isPullback_subscheme_sup I J).flip inferInstance
  have : LocallyOfFinitePresentation (I ⊔ J).subschemeι := by
    simpa [a] using (inferInstance : LocallyOfFinitePresentation (a ≫ I.subschemeι))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The closed subscheme cut out by a finite supremum of ideal sheaves whose closed subschemes are
of finite presentation is of finite presentation. -/
theorem finitePresentation_subschemeι_finsetSup {S : Scheme.{u}}
    {ι : Type*} (J : ι → S.IdealSheafData) (s : Finset ι)
    (hJ : ∀ i ∈ s, AlgebraicGeometry.FinitePresentation (J i).subschemeι) :
    AlgebraicGeometry.FinitePresentation (s.sup J).subschemeι := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    exact finitePresentation_subscheme_sup _ _ (hJ i (Finset.mem_insert_self ..))
      (ih fun j hj => hJ j (Finset.mem_insert_of_mem hj))

private theorem isOpen_forall_flatOverAt_above {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (I : S.IdealSheafData) :
    IsOpen {x : X | ∀ y : (pullback f I.subschemeι : Scheme.{u}),
      pullback.fst f I.subschemeι y = x →
      AlgebraicGeometry.IsFlatOverAt (pullback.snd f I.subschemeι).toLRSHom.toShHom
        ((modulePullback (pullback.fst f I.subschemeι).toLRSHom.toShHom).obj F) y} := by
  classical
  have hopen : IsOpen {y : (pullback f I.subschemeι : Scheme.{u}) |
      AlgebraicGeometry.IsFlatOverAt (pullback.snd f I.subschemeι).toLRSHom.toShHom
        ((modulePullback (pullback.fst f I.subschemeι).toLRSHom.toShHom).obj F) y} :=
    @AlgebraicGeometry.isOpen_setOf_isFlatOverAt_modulePullback _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback f I.subschemeι) F ‹F.IsQuasicoherent›
      ‹F.IsFinitePresentation› inferInstance
  convert ((pullback.fst f I.subschemeι).isClosedEmbedding.isClosedMap _
    hopen.isClosed_compl).isOpen_compl using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image]
  exact ⟨fun h ⟨y, hy, hxy⟩ => hy (h y hxy),
    fun h y hy => Classical.byContradiction fun hn => h ⟨y, hn, hy⟩⟩

/-- The pointed-base-change flatness condition along `E`, for a morphism `f : X ⟶ S` and a
module `F` on `X`: after the base change along `g : T ⟶ S`, the pulled-back module is flat over
`T` at every point of `X_T` above `t` whose image in `X` lies in `E`. -/
def FlatAlongAfter {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (E : Set X) {T : Scheme.{u}}
    (g : T ⟶ S) (t : T) : Prop :=
  ∀ y : pullback (C := Scheme.{u}) f g, pullback.snd f g y = t → pullback.fst f g y ∈ E →
    AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
      ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y

private theorem flatAlongAfter_iff_of_pointwise {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {F : X.Modules} {E : Set X}
    (J : E → (Spec (.of A)).IdealSheafData)
    (hJ : ∀ (x : E) {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T),
      g t = IsLocalRing.closedPoint A →
        ((∀ y : pullback (C := Scheme.{u}) f g, pullback.snd f g y = t →
            pullback.fst f g y = x.1 →
              AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
                ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) y) ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ (J x).subscheme,
            h ≫ (J x).subschemeι = T.fromSpecStalk t ≫ g))
    {I : (Spec (.of A)).IdealSheafData} (hJI : ∀ x, J x ≤ I)
    (hIle : ∀ K, (∀ x, J x ≤ K) → I ≤ K)
    {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T) (ht : g t = IsLocalRing.closedPoint A) :
    FlatAlongAfter f F E g t ↔
      ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme, h ≫ I.subschemeι = T.fromSpecStalk t ≫ g := by
  rw [exists_comp_subschemeι_eq_iff_le_ker]
  constructor
  · intro hflat
    refine hIle _ fun x => ?_
    rw [← exists_comp_subschemeι_eq_iff_le_ker]
    exact (hJ x g t ht).mp fun y hy hyx => hflat y hy (hyx ▸ x.2)
  · intro hle y hy hyE
    exact (hJ ⟨_, hyE⟩ g t ht).mpr ((exists_comp_subschemeι_eq_iff_le_ker _ _).mpr
      ((hJI ⟨_, hyE⟩).trans hle)) y hy rfl

/-- **The local flattening subscheme along a subset of the closed fibre** (the scheme case,
Stacks 05PI). Let `A` be a henselian local ring, `f : X ⟶ Spec A` locally of finite type, `F` a
quasi-coherent `𝒪_X`-module of finite type and `E` a set of points of `X` over the closed point.
There is a closed subscheme `Z ⊆ Spec A` such that for every pointed scheme
`(T, t) ⟶ (Spec A, s)` the module `F_T` is flat over `T` at all points of `X_T` above `t`
mapping into `E` exactly when `Spec 𝒪_{T,t} ⟶ Spec A` factors through `Z`. -/
theorem exists_idealSheafData_flatAlongAfter_iff (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (E : Set X) (hE : ∀ x ∈ E, f x = IsLocalRing.closedPoint A) :
    ∃ I : (Spec (.of A)).IdealSheafData,
      ∀ {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T), g t = IsLocalRing.closedPoint A →
        (FlatAlongAfter f F E g t ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
            h ≫ I.subschemeι = T.fromSpecStalk t ≫ g) := by
  classical
  let s : Spec (.of A) := IsLocalRing.closedPoint A
  have := isIso_fromSpecStalk_closedPoint (.of A)
  have : HenselianLocalRing ((Spec (.of A)).presheaf.stalk s) :=
    henselian_stalk_of_spec_local A
  have P (x : E) := exists_closedSubscheme_flatOverAt_iff_factorStalk f F x.1 s (hE x.1 x.2)
  choose J hJ using P
  exact ⟨⨆ x : E, J x, fun g t ht =>
    flatAlongAfter_iff_of_pointwise J hJ (le_iSup J) (fun _ hK => iSup_le hK) g t ht⟩

/-- **The local flattening subscheme along a subset of the closed fibre, finite presentation**
(the scheme case, Stacks 05PI). If moreover `f` is locally of finite presentation, `F` is of
finite presentation and `E` is closed and quasi-compact, the closed subscheme may be taken of
finite presentation over `Spec A`. -/
theorem exists_finitePresentation_idealSheafData_flatAlongAfter_iff (A : Type u) [CommRing A]
    [HenselianLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [F.IsFinitePresentation] (E : Set X) (hE : ∀ x ∈ E, f x = IsLocalRing.closedPoint A)
    (hEcompact : IsCompact E) :
    ∃ I : (Spec (.of A)).IdealSheafData,
      AlgebraicGeometry.FinitePresentation I.subschemeι ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T), g t = IsLocalRing.closedPoint A →
        (FlatAlongAfter f F E g t ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ I.subscheme,
            h ≫ I.subschemeι = T.fromSpecStalk t ≫ g) := by
  classical
  let s : Spec (.of A) := IsLocalRing.closedPoint A
  have := isIso_fromSpecStalk_closedPoint (.of A)
  have : HenselianLocalRing ((Spec (.of A)).presheaf.stalk s) :=
    henselian_stalk_of_spec_local A
  have hfp (x : X) : AlgebraicGeometry.FinitePresentationAt f x := by
    let V : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
        isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))⟩
    refine ⟨⟨⊤, isAffineOpen_top _⟩, V, X.affineCover.covers x, by simp, ?_⟩
    exact f.finitePresentation_appLE (isAffineOpen_top _) V.2 _
  have hstalk (x : X) : Module.FinitePresentation (X.presheaf.stalk x) (modulesStalk F x) :=
    @Stacks.SheafOfModules.finitePresentation_stalk X.toRingedSpace F ‹_› x
  have H (x : E) :=
    exists_finitePresentation_closedSubscheme_flatOverAt_iff_factorStalk
      f F x.1 s (hE x.1 x.2) (hfp _) (hstalk _)
  choose J hJfp hJ using H
  let U (x : E) : Set X := {z | ∀ y : (pullback f (J x).subschemeι : Scheme.{u}),
    pullback.fst f (J x).subschemeι y = z →
    AlgebraicGeometry.IsFlatOverAt (pullback.snd f (J x).subschemeι).toLRSHom.toShHom
      ((modulePullback (pullback.fst f (J x).subschemeι).toLRSHom.toShHom).obj F) y}
  have hUopen (x : E) : IsOpen (U x) := isOpen_forall_flatOverAt_above f F (J x)
  have hxU (x : E) : x.1 ∈ U x := by
    intro y hy
    have ht : (J x).subschemeι (pullback.snd f (J x).subschemeι y) = s := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hy]
      exact hE x.1 x.2
    exact (hJ x (J x).subschemeι _ ht).mpr
      ⟨(J x).subscheme.fromSpecStalk _, rfl⟩ y rfl hy
  -- a nonempty closed subscheme of `Spec A` has a point over the closed point whose
  -- canonical morphism from the spectrum of its stalk is an isomorphism
  have exists_closedPoint_iso_stalk : ∀ {T : Scheme.{u}} (i : T ⟶ Spec (.of A))
      [IsClosedImmersion i] [Nonempty T],
      ∃ t : T, i t = IsLocalRing.closedPoint A ∧ IsIso (T.fromSpecStalk t) := by
    intro T i _ _
    let : IsAffine T := isAffine_of_isAffineHom i
    let : Nonempty (⊤ : T.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    let φ : CommRingCat.of A ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (.of A)).inv ≫ i.appTop
    have hφ : Function.Surjective φ :=
      (i.app_surjective ⊤ (isAffineOpen_top _)).comp
        (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective
    let : IsLocalRing Γ(T, ⊤) := IsLocalRing.of_surjective' φ.hom hφ
    let : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hφ
    let p : Spec Γ(T, ⊤) := IsLocalRing.closedPoint Γ(T, ⊤)
    let t : T := T.isoSpec.inv p
    refine ⟨t, ?_, ?_⟩
    · show (T.isoSpec.inv ≫ i) p = _
      rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
      exact AlgebraicGeometry.Spec_closedPoint (f := φ)
    · have hnat := Scheme.SpecMap_stalkMap_fromSpecStalk T.isoSpec.inv (x := p)
      have := isIso_fromSpecStalk_closedPoint Γ(T, ⊤)
      have : IsIso (Spec.map (T.isoSpec.inv.stalkMap p) ≫ T.fromSpecStalk t) := by
        rw [hnat]
        infer_instance
      exact IsIso.of_isIso_comp_left (Spec.map (T.isoSpec.inv.stalkMap p)) _
  -- `I ≤ J` as soon as `J.subscheme ⟶ Spec A` factors through `I.subscheme` at the points over
  -- the closed point
  have le_of_pointed_stalk_factors : ∀ (I J : (Spec (.of A)).IdealSheafData),
      (∀ t : J.subscheme, J.subschemeι t = IsLocalRing.closedPoint A →
        ∃ h : Spec (J.subscheme.presheaf.stalk t) ⟶ I.subscheme,
          h ≫ I.subschemeι = J.subscheme.fromSpecStalk t ≫ J.subschemeι) → I ≤ J := by
    intro I J H
    cases isEmpty_or_nonempty J.subscheme with
    | inl h =>
      have : J = ⊤ := by
        rw [← Scheme.IdealSheafData.support_eq_bot_iff]
        apply SetLike.coe_injective
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact Set.range_eq_empty_iff.mpr h
      simp [this]
    | inr h =>
      obtain ⟨t, ht, h_iso⟩ := exists_closedPoint_iso_stalk J.subschemeι
      obtain ⟨a, ha⟩ := H t ht
      have hle := Scheme.Hom.le_ker_comp a I.subschemeι
      rw [Scheme.IdealSheafData.ker_subschemeι, ha,
        Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι] at hle
      exact hle
  have hle (x z : E) (hz : z.1 ∈ U x) : J z ≤ J x :=
    le_of_pointed_stalk_factors _ _ fun t ht =>
      (hJ z (J x).subschemeι t ht).mp fun y _ hy => hz y hy
  obtain ⟨a, ha⟩ := hEcompact.elim_finite_subcover U hUopen
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let I := a.sup J
  have hJI (z : E) : J z ≤ I := by
    obtain ⟨x, hx, hz⟩ := Set.mem_iUnion₂.mp (ha z.2)
    exact (hle x z hz).trans (Finset.le_sup hx)
  exact ⟨I, finitePresentation_subschemeι_finsetSup J a (fun x _ => hJfp x), fun g t ht =>
    flatAlongAfter_iff_of_pointwise J hJ hJI (fun _ hK => Finset.sup_le fun x _ => hK x) g t ht⟩

/-- Flatness of the pullback of a module over the new base at a point of a cartesian square is
read on Mathlib's chosen pullback, at the image of the point under the comparison isomorphism. -/
theorem isFlatOverAt_modulePullback_iff_of_isPullback {X S T P : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {a : P ⟶ X} {b : P ⟶ T} (h : IsPullback a b f g) (F : X.Modules) (y : P) :
    AlgebraicGeometry.IsFlatOverAt b.toLRSHom.toShHom ((modulePullback a.toLRSHom.toShHom).obj F)
        y ↔
      AlgebraicGeometry.IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
        ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) (h.isoPullback.hom y) := by
  let e := h.isoPullback.hom
  have heFlat : AlgebraicGeometry.IsFlatAt e.toLRSHom.toShHom y :=
    (Flat.iff_flat_stalkMap e).mp inferInstance y
  rw [isFlatOverAt_iff_modulePullback_isFlatOverAt e (pullback.snd f g) _ y heFlat]
  have hsnd : e ≫ pullback.snd f g = b := h.isoPullback_hom_snd
  have hfst : e ≫ pullback.fst f g = a := h.isoPullback_hom_fst
  have ecomp' :
      (modulePullback e.toLRSHom.toShHom).obj
          ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj F) ≅
        (modulePullback a.toLRSHom.toShHom).obj F := by
    rw [← hfst]
    exact (Scheme.Modules.pullbackComp e (pullback.fst f g)).app F
  rw [← hsnd]
  exact (isFlatOverAt_iff_of_moduleIso _ ecomp' y).symm

/-- `FlatAlongAfter` read on an arbitrary cartesian square in place of Mathlib's chosen
pullback. -/
theorem flatAlongAfter_iff_of_isPullback {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {b : P ⟶ T} (h : IsPullback a b f g) (F : X.Modules) (E : Set X) (t : T) :
    FlatAlongAfter f F E g t ↔
      ∀ y : P, b y = t → a y ∈ E →
        AlgebraicGeometry.IsFlatOverAt b.toLRSHom.toShHom
          ((modulePullback a.toLRSHom.toShHom).obj F) y := by
  have hsnd (y : P) : pullback.snd f g (h.isoPullback.hom y) = b y := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_snd]
  have hfst (y : P) : pullback.fst f g (h.isoPullback.hom y) = a y := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  constructor
  · intro H y hy hyE
    exact (isFlatOverAt_modulePullback_iff_of_isPullback h F y).mpr
      (H _ ((hsnd y).trans hy) ((hfst y).symm ▸ hyE))
  · intro H y hy hyE
    obtain ⟨y', rfl⟩ : ∃ y', h.isoPullback.hom y' = y :=
      ⟨h.isoPullback.inv y, by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl⟩
    exact (isFlatOverAt_modulePullback_iff_of_isPullback h F y').mp
      (H y' ((hsnd y').symm.trans hy) ((hfst y') ▸ hyE))

end AlgebraicGeometry.LocalFlattening
