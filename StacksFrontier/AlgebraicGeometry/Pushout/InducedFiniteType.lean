module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.InducedMorphism
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Local finite type for a morphism between pushouts along closed immersions

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions of schemes, let `f : X' ⟶ X` and
`g : Y' ⟶ Y` be arbitrary morphisms, and let an isomorphism over `Z` identify `X' ×_X Z` with
`Y' ×_Y Z`.  The two pieces `X'` and `Y'` then glue along their common inverse image of `Z`, and
the glued scheme maps to `Y ⨿_Z X`.  This file proves that the glued morphism is locally of
finite type exactly when `f` and `g` are.

## Main results

* `AlgebraicGeometry.induced_locallyOfFiniteType_iff`: the induced morphism between the two
  pushouts is locally of finite type if and only if both of its pieces are.

## Implementation notes

The vertex of the cartesian square of a ring fibre product has to be identified with the subring
`RingHom.pullback`, and instance search does not see through the cone to do it; the two cone
constructors are therefore made locally reducible.

## References

* [Stacks Project, Tag 0CYY](https://stacks.math.columbia.edu/tag/0CYY)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local implicit_reducible] CommRingCat.pullbackCone
  CategoryTheory.Limits.PullbackCone.mk CategoryTheory.IsPullback.cone
  CategoryTheory.CommSq.cone

namespace AlgebraicGeometry

/-- Affine charts of a cartesian square of schemes give a pushout square of rings of sections: if
`W` is the fibre product of `X` and `Y` over `Z`, the four opens are affine and compatible, and
the open in `W` is the intersection of the inverse images of the opens in `X` and `Y`, then the
square of restriction maps on sections is a pushout square of rings. -/
private theorem isPushout_appLE_of_isPullback
    {X Y Z W : Scheme.{u}} {g : W ⟶ X} {iY : W ⟶ Y} {iX : X ⟶ Z} {f : Y ⟶ Z}
    (H : IsPullback g iY iX f)
    (UZ : Z.Opens) (hUZ : IsAffineOpen UZ)
    (UY : Y.Opens) (hUY : IsAffineOpen UY) (hUYle : UY ≤ f ⁻¹ᵁ UZ)
    (UX : X.Opens) (hUX : IsAffineOpen UX) (hUXle : UX ≤ iX ⁻¹ᵁ UZ)
    (UW : W.Opens) (hUW : UW = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UY) (hUWaff : IsAffineOpen UW) :
    IsPushout (f.appLE UZ UY hUYle) (iX.appLE UZ UX hUXle)
      (iY.appLE UY UW (by rw [hUW]; simp)) (g.appLE UX UW (by rw [hUW]; simp)) := by
  have hres := Scheme.Hom.isPullback_resLE H hUYle hUXle hUW
  have hSpec : IsPullback
      (Scheme.Spec.map ((iY.appLE UY UW (by rw [hUW]; simp)).op))
      (Scheme.Spec.map ((g.appLE UX UW (by rw [hUW]; simp)).op))
      (Scheme.Spec.map ((f.appLE UZ UY hUYle).op))
      (Scheme.Spec.map ((iX.appLE UZ UX hUXle).op)) :=
    .of_iso hres.flip hUWaff.isoSpec hUY.isoSpec hUX.isoSpec hUZ.isoSpec
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE iY UY UW (by rw [hUW]; simp)).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE g UX UW (by rw [hUW]; simp)).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE f UZ UY hUYle).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE iX UZ UX hUXle).symm)
  exact (IsPullback.of_map_of_faithful Scheme.Spec hSpec).unop.flip

/-- A map between the vertices of two cartesian squares of rings is of finite type as soon as its
two components are, provided the right-hand map of the lower square is surjective and the upper
square is obtained from the lower one by two pushouts.  This is the finite-type assertion of
[Stacks Project, Tag 08KQ], transported from the canonical fibre product to an arbitrary
cartesian square. -/
private theorem finiteType_of_isPullback_of_isPushout
    {A A' B C C' D P Q : CommRingCat.{u}}
    {toBase : B ⟶ A} {surjection : A' ⟶ A} {AtoC : A ⟶ C}
    {BtoD : B ⟶ D} {A'toC' : A' ⟶ C'} {DtoC : D ⟶ C} {C'toC : C' ⟶ C}
    {pB : P ⟶ B} {pA' : P ⟶ A'} {qD : Q ⟶ D} {qC' : Q ⟶ C'} {m : P ⟶ Q}
    (hsurj : Function.Surjective surjection.hom)
    (hD : IsPushout BtoD toBase DtoC AtoC)
    (hC : IsPushout A'toC' surjection C'toC AtoC)
    (hP : IsPullback pB pA' toBase surjection)
    (hQ : IsPullback qD qC' DtoC C'toC)
    (hmD : m ≫ qD = pB ≫ BtoD) (hmC : m ≫ qC' = pA' ≫ A'toC')
    (hBD : BtoD.hom.FiniteType) (hAC : A'toC'.hom.FiniteType) :
    m.hom.FiniteType := by
  let base : RingFibreProduct.Situation toBase.hom surjection.hom
      (RingHom.ker surjection.hom) := ⟨hsurj, rfl⟩
  have hDr : MilnorPatching.ringPushout BtoD.hom toBase.hom DtoC.hom AtoC.hom :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _ hD
  have hCr : MilnorPatching.ringPushout A'toC'.hom surjection.hom C'toC.hom AtoC.hom :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _ hC
  have hpatch := MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction
    toBase.hom surjection.hom (RingHom.ker surjection.hom) base
    BtoD.hom A'toC'.hom AtoC.hom DtoC.hom C'toC.hom hDr hCr
  let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
  let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC.hom C'toC.hom :=
    RingHom.codRestrict ((BtoD.hom.comp toB).prod (A'toC'.hom.comp toA'))
      (RingHom.pullback DtoC.hom C'toC.hom) (fun x ↦ by
        show DtoC.hom (BtoD.hom (toB x)) = C'toC.hom (A'toC'.hom (toA' x))
        calc
          _ = AtoC.hom (toBase.hom (toB x)) :=
            DFunLike.congr_fun (MilnorPatching.ringPushout_comm hDr) (toB x)
          _ = AtoC.hom (surjection.hom (toA' x)) := congrArg AtoC.hom
            (DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
          _ = _ := (DFunLike.congr_fun (MilnorPatching.ringPushout_comm hCr) (toA' x)).symm)
  have htoD' : toD'.FiniteType := by simpa [toD', toB, toA'] using hpatch.1.mpr ⟨hBD, hAC⟩
  let eP := (base.pullbackConeIsLimit.conePointUniqueUpToIso hP.isLimit).symm
  let sourceCone := CommRingCat.pullbackCone DtoC C'toC
  let sourceLim := CommRingCat.pullbackConeIsLimit DtoC C'toC
  let eQ := (sourceLim.conePointUniqueUpToIso hQ.isLimit).symm
  have hePB : eP.hom ≫ base.pullbackCone.fst = pB :=
    IsLimit.conePointUniqueUpToIso_inv_comp base.pullbackConeIsLimit hP.isLimit
      WalkingCospan.left
  have hePA : eP.hom ≫ base.pullbackCone.snd = pA' :=
    IsLimit.conePointUniqueUpToIso_inv_comp base.pullbackConeIsLimit hP.isLimit
      WalkingCospan.right
  have heQD : eQ.hom ≫ sourceCone.fst = qD :=
    IsLimit.conePointUniqueUpToIso_inv_comp sourceLim hQ.isLimit WalkingCospan.left
  have heQC : eQ.hom ≫ sourceCone.snd = qC' :=
    IsLimit.conePointUniqueUpToIso_inv_comp sourceLim hQ.isLimit WalkingCospan.right
  have hmapIso : eP.hom ≫ CommRingCat.ofHom toD' = m ≫ eQ.hom := by
    apply PullbackCone.IsLimit.hom_ext sourceLim
    · have htoDfst : CommRingCat.ofHom toD' ≫ sourceCone.fst =
          CommRingCat.ofHom (BtoD.hom.comp toB) := by
        ext x
        rfl
      calc
        (eP.hom ≫ CommRingCat.ofHom toD') ≫ sourceCone.fst =
            eP.hom ≫ CommRingCat.ofHom (BtoD.hom.comp toB) := by
          rw [Category.assoc, htoDfst]
        _ = (eP.hom ≫ base.pullbackCone.fst) ≫ BtoD := rfl
        _ = pB ≫ BtoD := by rw [hePB]
        _ = (m ≫ eQ.hom) ≫ sourceCone.fst := by
          rw [Category.assoc, heQD]
          exact hmD.symm
    · have htoDsnd : CommRingCat.ofHom toD' ≫ sourceCone.snd =
          CommRingCat.ofHom (A'toC'.hom.comp toA') := by
        ext x
        rfl
      calc
        (eP.hom ≫ CommRingCat.ofHom toD') ≫ sourceCone.snd =
            eP.hom ≫ CommRingCat.ofHom (A'toC'.hom.comp toA') := by
          rw [Category.assoc, htoDsnd]
        _ = (eP.hom ≫ base.pullbackCone.snd) ≫ A'toC' := rfl
        _ = pA' ≫ A'toC' := by rw [hePA]
        _ = (m ≫ eQ.hom) ≫ sourceCone.snd := by
          rw [Category.assoc, heQC]
          exact hmC.symm
  have hiso : Arrow.mk m ≅ Arrow.mk (CommRingCat.ofHom toD') := Arrow.isoMk eP eQ hmapIso
  exact (RingHom.finiteType_respectsIso.arrow_mk_iso_iff hiso).mpr htoD'

/-- If `a' ≫ h = f ≫ a`, then `h` maps `U ≤ h ⁻¹ᵁ V` into `V` compatibly with `f` and `a`. -/
private theorem preimage_le_of_comp_eq {X' X P P' : Scheme.{u}} {f : X' ⟶ X} {a : X ⟶ P}
    {a' : X' ⟶ P'} {h : P' ⟶ P} (hcomp : a' ≫ h = f ≫ a) {V : P.Opens} {U : P'.Opens}
    (hUV : U ≤ h ⁻¹ᵁ V) : a' ⁻¹ᵁ U ≤ f ⁻¹ᵁ (a ⁻¹ᵁ V) := by
  intro x hx
  change (f ≫ a) x ∈ V
  rw [← hcomp]
  exact hUV hx

/-- The restriction maps of `h` and `f` on sections are compatible with `a` and `a'`, when
`a' ≫ h = f ≫ a`. -/
private theorem appLE_comp_app_eq {X' X P P' : Scheme.{u}} {f : X' ⟶ X} {a : X ⟶ P}
    {a' : X' ⟶ P'} {h : P' ⟶ P} (hcomp : a' ≫ h = f ≫ a) {V : P.Opens} {U : P'.Opens}
    (hUV : U ≤ h ⁻¹ᵁ V) (hbase : a' ⁻¹ᵁ U ≤ f ⁻¹ᵁ (a ⁻¹ᵁ V)) :
    h.appLE V U hUV ≫ a'.app U = a.app V ≫ f.appLE (a ⁻¹ᵁ V) (a' ⁻¹ᵁ U) hbase := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  refine (Scheme.Hom.appLE_comp_appLE a' h V U (a' ⁻¹ᵁ U) hUV le_rfl).trans ?_
  refine (appLE_eq_appLE_of_eq hcomp V (a' ⁻¹ᵁ U) (a'.preimage_mono hUV) hbase).trans ?_
  exact (Scheme.Hom.appLE_comp_appLE f a V (a ⁻¹ᵁ V) (a' ⁻¹ᵁ U) le_rfl hbase).symm

/-- For a pushout square `i, j, a, b` of schemes with `i`, `j` closed immersions and `a` affine,
the sections over `V` form a cartesian square, with `i` and `j` restricted to
`j ⁻¹ᵁ (b ⁻¹ᵁ V)`. -/
private theorem isPullback_appLE_of_isPushout {Z X Y P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsClosedImmersion j] [IsAffineHom a]
    (hT : IsPushout i j a b) (V : P.Opens)
    (hle : j ⁻¹ᵁ (b ⁻¹ᵁ V) ≤ i ⁻¹ᵁ (a ⁻¹ᵁ V)) :
    IsPullback (b.app V) (a.app V) (j.appLE (b ⁻¹ᵁ V) (j ⁻¹ᵁ (b ⁻¹ᵁ V)) le_rfl)
      (i.appLE (a ⁻¹ᵁ V) (j ⁻¹ᵁ (b ⁻¹ᵁ V)) hle) := by
  have heV : i ⁻¹ᵁ (a ⁻¹ᵁ V) = j ⁻¹ᵁ (b ⁻¹ᵁ V) := congrArg (fun k : Z ⟶ P ↦ k ⁻¹ᵁ V) hT.w
  rw [Scheme.Hom.appLE_eq_app, ← app_comp_eqToHom_eq_appLE i heV hle]
  exact structureSheaf_isPullback_of_isPushout_of_isAffineHom hT V

/-- For a morphism `h` between two pushout squares along closed immersions whose two component
squares are cartesian, the restriction map on sections over a pair of affine opens is of finite
type as soon as the two components are locally of finite type. -/
private theorem finiteType_appLE_of_isPushout
    {Z X Y Z' X' Y' P P' : Scheme.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {i' : Z' ⟶ X'} {j' : Z' ⟶ Y'} {φ : Z' ⟶ Z}
    {f : X' ⟶ X} {g : Y' ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} {a' : X' ⟶ P'} {b' : Y' ⟶ P'} {h : P' ⟶ P}
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion i'] [IsClosedImmersion j']
    [IsAffineHom a] [IsAffineHom b] [IsAffineHom a'] [IsAffineHom b']
    (hT : IsPushout i j a b) (hQ : IsPushout i' j' a' b')
    (hX : IsPullback i' φ f i) (hY : IsPullback j' φ g j)
    (hcompX : a' ≫ h = f ≫ a) (hcompY : b' ≫ h = g ≫ b)
    (hf : LocallyOfFiniteType f) (hg : LocallyOfFiniteType g)
    {V : P.Opens} (hV : IsAffineOpen V) {U : P'.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ h ⁻¹ᵁ V) :
    (h.appLE V U hUV).hom.FiniteType := by
  have hVx : IsAffineOpen (a ⁻¹ᵁ V) := hV.preimage a
  have hVy : IsAffineOpen (b ⁻¹ᵁ V) := hV.preimage b
  have hVz : IsAffineOpen (j ⁻¹ᵁ (b ⁻¹ᵁ V)) := hVy.preimage j
  have hUx : IsAffineOpen (a' ⁻¹ᵁ U) := hU.preimage a'
  have hUy : IsAffineOpen (b' ⁻¹ᵁ U) := hU.preimage b'
  have hUz : IsAffineOpen (j' ⁻¹ᵁ (b' ⁻¹ᵁ U)) := hUy.preimage j'
  have heV : i ⁻¹ᵁ (a ⁻¹ᵁ V) = j ⁻¹ᵁ (b ⁻¹ᵁ V) := congrArg (fun k : Z ⟶ P ↦ k ⁻¹ᵁ V) hT.w
  have heU : i' ⁻¹ᵁ (a' ⁻¹ᵁ U) = j' ⁻¹ᵁ (b' ⁻¹ᵁ U) :=
    congrArg (fun k : Z' ⟶ P' ↦ k ⁻¹ᵁ U) hQ.w
  have hVzle : j ⁻¹ᵁ (b ⁻¹ᵁ V) ≤ i ⁻¹ᵁ (a ⁻¹ᵁ V) := heV.ge
  have hUzle : j' ⁻¹ᵁ (b' ⁻¹ᵁ U) ≤ i' ⁻¹ᵁ (a' ⁻¹ᵁ U) := heU.ge
  have hXbase := preimage_le_of_comp_eq hcompX hUV
  have hYbase := preimage_le_of_comp_eq hcompY hUV
  have hUzφ : j' ⁻¹ᵁ (b' ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (j ⁻¹ᵁ (b ⁻¹ᵁ V)) := by
    intro z hz
    show (φ ≫ j) z ∈ b ⁻¹ᵁ V
    rw [← hY.w]
    exact hYbase hz
  have hUzX : j' ⁻¹ᵁ (b' ⁻¹ᵁ U) =
      φ ⁻¹ᵁ (j ⁻¹ᵁ (b ⁻¹ᵁ V)) ⊓ i' ⁻¹ᵁ (a' ⁻¹ᵁ U) := by
    rw [heU]
    exact (inf_eq_right.mpr hUzφ).symm
  have hDpush := isPushout_appLE_of_isPullback hY.flip (b ⁻¹ᵁ V) hVy (b' ⁻¹ᵁ U) hUy hYbase
    (j ⁻¹ᵁ (b ⁻¹ᵁ V)) hVz le_rfl (j' ⁻¹ᵁ (b' ⁻¹ᵁ U)) (inf_eq_right.mpr hUzφ).symm hUz
  have hCpush := isPushout_appLE_of_isPullback hX.flip (a ⁻¹ᵁ V) hVx (a' ⁻¹ᵁ U) hUx hXbase
    (j ⁻¹ᵁ (b ⁻¹ᵁ V)) hVz hVzle (j' ⁻¹ᵁ (b' ⁻¹ᵁ U)) hUzX hUz
  have htargetPB' := isPullback_appLE_of_isPushout hT V hVzle
  have hsourcePB' := isPullback_appLE_of_isPushout hQ U hUzle
  have hsurj : Function.Surjective
      (i.appLE (a ⁻¹ᵁ V) (j ⁻¹ᵁ (b ⁻¹ᵁ V)) hVzle).hom := by
    rw [← app_comp_eqToHom_eq_appLE i heV hVzle]
    show Function.Surjective
      ((eqToHom (congrArg (fun W ↦ Γ(Z, W)) heV)).hom ∘ (i.app (a ⁻¹ᵁ V)).hom)
    exact Function.Surjective.comp
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (congrArg (fun W ↦ Γ(Z, W)) heV))).2
      (i.app_surjective (a ⁻¹ᵁ V) hVx)
  exact finiteType_of_isPullback_of_isPushout hsurj hDpush hCpush htargetPB' hsourcePB'
    (appLE_comp_app_eq hcompY hUV hYbase) (appLE_comp_app_eq hcompX hUV hXbase)
    (hg.finiteType_appLE hVy hUy hYbase)
    (hf.finiteType_appLE hVx hUx hXbase)

/-- The induced morphism is compatible with the two pieces and the two pushout inclusions. -/
private theorem induced_comp_eqs (S : CompatiblePushoutMorphismSituation.{u}) :
    pushout.inl S.toX' S.toY' ≫ S.induced = S.f ≫ pushout.inl S.i S.j ∧
      pushout.inr S.toX' S.toY' ≫ S.induced = S.g ≫ pushout.inr S.i S.j := by
  exact ⟨by rw [CompatiblePushoutMorphismSituation.induced, pushout.inl_desc],
    by rw [CompatiblePushoutMorphismSituation.induced, pushout.inr_desc]⟩

/-- The induced morphism between the two pushouts is locally of finite type as soon as both of
its pieces are. -/
private theorem induced_locallyOfFiniteType (S : CompatiblePushoutMorphismSituation.{u})
    (hf : LocallyOfFiniteType S.f) (hg : LocallyOfFiniteType S.g) :
    LocallyOfFiniteType S.induced := by
  have hT : IsPushout S.i S.j (pushout.inl S.i S.j) (pushout.inr S.i S.j) :=
    IsPushout.of_hasPushout S.i S.j
  have hQ : IsPushout S.toX' S.toY' (pushout.inl S.toX' S.toY')
      (pushout.inr S.toX' S.toY') := IsPushout.of_hasPushout S.toX' S.toY'
  have hX : IsPullback S.toX' (pullback.snd S.f S.i) S.f S.i :=
    IsPullback.of_hasPullback S.f S.i
  have hY : IsPullback S.toY' (pullback.snd S.f S.i) S.g S.j := by
    rw [← S.φ_over]
    exact (IsPullback.of_hasPullback S.g S.j).of_iso S.φ.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨hcompX, hcompY⟩ := induced_comp_eqs S
  refine ⟨?_⟩
  intro V hV U hU hUV
  exact finiteType_appLE_of_isPushout hT hQ hX hY hcompX hcompY hf hg hV hU hUV

/-- In the situation of two closed immersions `i : Z ⟶ X` and `j : Z ⟶ Y`, morphisms
`f : X' ⟶ X` and `g : Y' ⟶ Y`, and an isomorphism over `Z` between the two inverse images of `Z`,
the induced morphism from the glued scheme `X' ⨿_{X' ×_X Z} Y'` to the pushout `Y ⨿_Z X` is
locally of finite type if and only if `f` and `g` are locally of finite type. -/
@[stacks 0CYY "locally_of_finite_type"]
theorem induced_locallyOfFiniteType_iff (S : CompatiblePushoutMorphismSituation.{u}) :
    LocallyOfFiniteType S.induced ↔
      LocallyOfFiniteType S.f ∧ LocallyOfFiniteType S.g := by
  refine ⟨fun hh ↦ ?_, fun hh ↦ induced_locallyOfFiniteType S hh.1 hh.2⟩
  obtain ⟨hcompX, hcompY⟩ := induced_comp_eqs S
  let : LocallyOfFiniteType S.induced := hh
  have : LocallyOfFiniteType (S.f ≫ pushout.inl S.i S.j) := by
    rw [← hcompX]; infer_instance
  have : LocallyOfFiniteType (S.g ≫ pushout.inr S.i S.j) := by
    rw [← hcompY]; infer_instance
  exact ⟨locallyOfFiniteType_of_comp S.f (pushout.inl S.i S.j),
    locallyOfFiniteType_of_comp S.g (pushout.inr S.i S.j)⟩

end AlgebraicGeometry

end
