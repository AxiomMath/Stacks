module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QuasiSeparated
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# The induction principle on a scheme

Auxiliary material for the induction principle on quasi-compact quasi-separated algebraic
spaces: the fibre product of two subfunctor inclusions, the isomorphism-invariant
strengthening of the property, its passage across one
elementary distinguished square, and its propagation over the quasi-compact opens of an
étale object which is a scheme, by induction on those opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_schemeCase {B : BigFppfSite} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_schemeCase
    {B : BigFppfSite} {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- The fibre product of the inclusions of two subfunctors is the inclusion of their
intersection. -/
private noncomputable def pullbackInfIso
    {C : Type v} [Category C] {F : Cᵒᵖ ⥤ Type u}
    (A D : Subfunctor F) :
    pullback A.ι D.ι ≅ (A ⊓ D).toFunctor := by
  let I : Subfunctor F := A ⊓ D
  let i : I.toFunctor ⟶ pullback A.ι D.ι :=
    pullback.lift (Subfunctor.homOfLe inf_le_left)
      (Subfunctor.homOfLe inf_le_right) (by
        simp)
  let j : pullback A.ι D.ι ⟶ I.toFunctor :=
    I.lift (pullback.fst A.ι D.ι ≫ A.ι) (by
      intro T x hx
      rcases hx with ⟨y, rfl⟩
      change A.ι.app T ((pullback.fst A.ι D.ι).app T y) ∈ A.obj T ∧
        A.ι.app T ((pullback.fst A.ι D.ι).app T y) ∈ D.obj T
      constructor
      · exact ((pullback.fst A.ι D.ι).app T y).property
      · have heq : A.ι.app T ((pullback.fst A.ι D.ι).app T y) =
            D.ι.app T ((pullback.snd A.ι D.ι).app T y) :=
          congrArg (fun k => k.app T y) (pullback.condition (f := A.ι) (g := D.ι))
        rw [heq]
        exact ((pullback.snd A.ι D.ι).app T y).property)
  refine ⟨j, i, ?_, ?_⟩
  · apply pullback.hom_ext
    · have hcomp : (j ≫ i ≫ pullback.fst A.ι D.ι) ≫ A.ι =
          pullback.fst A.ι D.ι ≫ A.ι := by
        calc
        (j ≫ i ≫ pullback.fst A.ι D.ι) ≫ A.ι =
            j ≫ (i ≫ pullback.fst A.ι D.ι) ≫ A.ι := by simp [Category.assoc]
        _ = j ≫ Subfunctor.homOfLe (inf_le_left : I ≤ A) ≫ A.ι := by
          simp only [i, pullback.lift_fst]
        _ = j ≫ I.ι := by rw [Subfunctor.homOfLe_ι]
        _ = pullback.fst A.ι D.ι ≫ A.ι := by
          change I.lift _ _ ≫ I.ι = _
          exact Subfunctor.lift_ι _ _
      exact (cancel_mono A.ι).mp hcomp
    · have hcomp : (j ≫ i ≫ pullback.snd A.ι D.ι) ≫ D.ι =
          pullback.snd A.ι D.ι ≫ D.ι := by
        calc
        (j ≫ i ≫ pullback.snd A.ι D.ι) ≫ D.ι =
            j ≫ (i ≫ pullback.snd A.ι D.ι) ≫ D.ι := by simp [Category.assoc]
        _ = j ≫ Subfunctor.homOfLe (inf_le_right : I ≤ D) ≫ D.ι := by
          simp only [i, pullback.lift_snd]
        _ = j ≫ I.ι := by rw [Subfunctor.homOfLe_ι]
        _ = pullback.snd A.ι D.ι ≫ D.ι := by
          calc
            j ≫ I.ι = pullback.fst A.ι D.ι ≫ A.ι := by
              change I.lift _ _ ≫ I.ι = _
              exact Subfunctor.lift_ι _ _
            _ = pullback.snd A.ι D.ι ≫ D.ι := pullback.condition
      exact (cancel_mono D.ι).mp hcomp
  · ext T x
    apply Subtype.ext
    change (i ≫ pullback.fst A.ι D.ι ≫ A.ι).app T x = I.ι.app T x
    have h : i ≫ pullback.fst A.ι D.ι ≫ A.ι = I.ι := by
      have hi : i ≫ pullback.fst A.ι D.ι =
          Subfunctor.homOfLe (inf_le_left : I ≤ A) := by
        dsimp [i]
        exact pullback.lift_fst _ _ _
      change (i ≫ pullback.fst A.ι D.ι) ≫ A.ι = I.ι
      rw [hi]
      exact Subfunctor.homOfLe_ι _
    rw [h]

/-- The property obtained from `P` by demanding it of every presheaf isomorphic to the given
one, with the isomorphism folded into the structure morphism. -/
def propertyUpToIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop) :
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.1) → Prop :=
  fun Y g => ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (e : Z ≅ Y), P Z (e.hom ≫ g)

/-- On an affine object of the spaces-étale site the isomorphism-invariant form of `P` follows
from `P` on affine objects. -/
theorem propertyUpToIso_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        P V.1.left.1 V.1.hom.hom)
    (V : SpacesEtale B S hS X)
    (hVaff : IsAffineSpace B S hS V.1.left.1) :
    propertyUpToIso B S hS X P V.1.left.1 V.1.hom.hom := by
  intro Z e
  let hZ : IsAlgebraicSpace B S hS Z :=
    IsAlgebraicSpace.of_iso V.1.left.property e.symm
  let V' := siteObjectOfEtaleMap B S hS X Z hZ
    (e.hom ≫ V.1.hom.hom)
    (isEtale_comp B S hS
      (etale_of_iso_presheaves B S hS e) V.2)
  exact haff V' (by
    rcases hVaff with ⟨A, hA, ⟨i⟩⟩
    exact ⟨A, hA, ⟨e ≪≫ i⟩⟩)

/-- The morphism from the preimage of a subfunctor along an isomorphism is an isomorphism. -/
theorem fromPreimage_isIso_of_isIso
    {C : Type _} [Category C] {F G : Cᵒᵖ ⥤ Type _}
    (U : Subfunctor G) (e : F ≅ G) : IsIso (U.fromPreimage e.hom) := by
  have hbij (T : C) : Function.Bijective ((U.fromPreimage e.hom).app (Opposite.op T)) := by
    constructor
    · intro x y hxy
      have hval : e.hom.app (Opposite.op T) x.val =
          e.hom.app (Opposite.op T) y.val := congrArg Subtype.val hxy
      have hinj : Function.Injective (e.hom.app (Opposite.op T)) := by
        intro a b hab
        have h' := congrArg (e.inv.app (Opposite.op T)) hab
        simpa using h'
      apply Subtype.ext
      exact hinj hval
    · intro y
      refine ⟨⟨e.inv.app (Opposite.op T) y.1, ?_⟩, ?_⟩
      · change e.hom.app (Opposite.op T) (e.inv.app (Opposite.op T) y.1) ∈ U.obj _
        simpa using y.2
      · apply Subtype.ext
        change e.hom.app (Opposite.op T) (e.inv.app (Opposite.op T) y.1) = y.1
        simp
  let : ∀ T : C, IsIso ((U.fromPreimage e.hom).app (Opposite.op T)) := by
    intro T
    rw [isIso_iff_bijective]
    exact hbij T
  exact NatIso.isIso_of_isIso_app (U.fromPreimage e.hom)

/-- The inductive step across an elementary distinguished square, in its
isomorphism-invariant form. -/
private theorem propertyUpToIso_step
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      (f ≫ W.1.hom.hom = V.1.hom.hom) →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom)
    (W V : SpacesEtale B S hS X)
    (U : Subfunctor W.1.left.1)
    (f : V.1.left.1 ⟶ W.1.left.1)
    (hcomp : f ≫ W.1.hom.hom = V.1.hom.hom)
    (hsq : IsElementaryDistinguishedSquare B S hS W.1.left.property U f)
    (hWqc : IsQuasiCompactSpace B S hS W.1.left.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVaff : IsAffineSpace B S hS V.1.left.1)
    (hQU : propertyUpToIso B S hS X P U.toFunctor
      (U.ι ≫ W.1.hom.hom))
    (hQV : propertyUpToIso B S hS X P V.1.left.1 V.1.hom.hom)
    (hQpb : propertyUpToIso B S hS X P (pullback U.ι f)
      (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom)) :
    propertyUpToIso B S hS X P W.1.left.1 W.1.hom.hom := by
  intro Z e
  let U' := U.preimage e.hom
  let k := U.fromPreimage e.hom
  have hk : IsIso k := fromPreimage_isIso_of_isIso U e
  let V' := pullback f e.hom
  let f' := pullback.snd f e.hom
  have hsq' := isElementaryDistinguishedSquare_preimage
    B S hS W.1.left.property (IsAlgebraicSpace.of_iso W.1.left.property e.symm)
    U f hsq e.hom
  have hZqc : IsQuasiCompactSpace B S hS Z :=
    IsQuasiCompactSpace.of_iso B S hS hWqc e.symm
  have hZqs : IsAbsolutelyQuasiSeparated B S hS hZ Z := by
    let q : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
    let R := OverShriek.relocalizePresheafFunctor q
    change IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ
      (viewOverIntegers B S hS hZ Z)
    apply qs_preserved_by_iso B (⊤_ Scheme.{u}) hZ (R.mapIso e.symm)
    change IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ
      (viewOverIntegers B S hS hZ W.1.left.1) at hWqs
    exact hWqs
  have hU'qc : IsQuasiCompactSpace B S hS U'.toFunctor :=
    IsQuasiCompactSpace.of_iso B S hS hUqc (asIso k).symm
  have hV'iso : IsIso (pullback.fst f e.hom) := by
    apply IsPullback.isIso_fst_of_isIso
      (IsPullback.of_isLimit (pullbackIsPullback f e.hom))
  let Walg : AlgebraicSpaces B S hS :=
    ⟨Z, IsAlgebraicSpace.of_iso W.1.left.property e.symm⟩
  let Valg : AlgebraicSpaces B S hS :=
    ⟨V', isAlgebraicSpace_pullback B S hS f e.hom
      V.1.left.property Walg.property W.1.left.property⟩
  have hEtale' : IsEtale B S hS f' := hsq'.isEtale
  have hV'aff : IsAffineSpace B S hS Valg.1 := by
    let : IsIso (pullback.fst f e.hom) := hV'iso
    rcases hVaff with ⟨A, hA, ⟨i⟩⟩
    exact ⟨A, hA, ⟨(asIso (pullback.fst f e.hom)) ≪≫ i⟩⟩
  have hUmap : U'.ι ≫ (e.hom ≫ W.1.hom.hom) =
      k ≫ U.ι ≫ W.1.hom.hom := by
    calc
      U'.ι ≫ (e.hom ≫ W.1.hom.hom) = (U'.ι ≫ e.hom) ≫ W.1.hom.hom := by
        simp [Category.assoc]
      _ = (k ≫ U.ι) ≫ W.1.hom.hom := by rw [Subfunctor.fromPreimage_ι]
      _ = k ≫ U.ι ≫ W.1.hom.hom := by simp [Category.assoc]
  have hVmap : f' ≫ (e.hom ≫ W.1.hom.hom) =
      pullback.fst f e.hom ≫ V.1.hom.hom := by
    calc
      f' ≫ (e.hom ≫ W.1.hom.hom) = (f' ≫ e.hom) ≫ W.1.hom.hom := by
        simp [Category.assoc]
      _ = (pullback.fst f e.hom ≫ f) ≫ W.1.hom.hom := by
        rw [← pullback.condition]
      _ = pullback.fst f e.hom ≫ V.1.hom.hom := by
        calc
          (pullback.fst f e.hom ≫ f) ≫ W.1.hom.hom =
              pullback.fst f e.hom ≫ (f ≫ W.1.hom.hom) := by simp [Category.assoc]
          _ = pullback.fst f e.hom ≫ V.1.hom.hom := by rw [hcomp]
  have hPU' : P U'.toFunctor
      (U'.ι ≫ (e.hom ≫ W.1.hom.hom)) := by
    rw [hUmap]
    exact hQU U'.toFunctor (asIso k)
  have hPV' : P V' (f' ≫ (e.hom ≫ W.1.hom.hom)) := by
    rw [hVmap]
    exact hQV V' (asIso (pullback.fst f e.hom))
  let pbIsoMap := pullback.map U'.ι f' U.ι f k (pullback.fst f e.hom) e.hom
    (by simpa [k, f', U'] using (Subfunctor.fromPreimage_ι U e.hom).symm)
    (by
      dsimp [f']
      rw [pullback.condition])
  have hpbIsoMap : IsIso pbIsoMap := by infer_instance
  have hPpb' : P (pullback U'.ι f')
      (pullback.fst U'.ι f' ≫ U'.ι ≫ (e.hom ≫ W.1.hom.hom)) := by
    let e' := asIso pbIsoMap
    have hmap : pbIsoMap ≫ pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom =
        pullback.fst U'.ι f' ≫ U'.ι ≫ (e.hom ≫ W.1.hom.hom) := by
      calc
        pbIsoMap ≫ pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom =
            (pullback.fst U'.ι f' ≫ k) ≫ U.ι ≫ W.1.hom.hom := by
          dsimp [pbIsoMap, pullback.map]
          rw [← Category.assoc, pullback.lift_fst]
        _ = pullback.fst U'.ι f' ≫ (k ≫ U.ι) ≫ W.1.hom.hom := by
          simp [Category.assoc]
        _ = pullback.fst U'.ι f' ≫ (U'.ι ≫ e.hom) ≫ W.1.hom.hom := by
          rw [Subfunctor.fromPreimage_ι]
        _ = pullback.fst U'.ι f' ≫ U'.ι ≫ (e.hom ≫ W.1.hom.hom) := by
          simp [Category.assoc]
    rw [← hmap]
    exact hQpb (pullback U'.ι f') e'
  let W' := siteObjectOfEtaleMap B S hS X Z Walg.property
      (e.hom ≫ W.1.hom.hom)
      (isEtale_comp B S hS
        (etale_of_iso_presheaves B S hS e) W.2)
  let V'' := siteObjectOfEtaleMap B S hS X Valg.1 Valg.property
      (f' ≫ W'.1.hom.hom)
      (isEtale_comp B S hS hEtale' W'.2)
  have hcomp' : f' ≫ W'.1.hom.hom = V''.1.hom.hom := rfl
  exact hstep W' V'' U' f' hcomp' hsq' hZqc hZqs hU'qc hV'aff hPU' hPV' hPpb'

/-- The isomorphism-invariant form of `P` holds on the subfunctor cut out by any quasi-compact
open of an étale object of the site which is a scheme. -/
private theorem propertyUpToIso_on_compact_open_of_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 → P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom)
    (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) (hg : IsEtale B S hS g)
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T)]
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))
    (A : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hA : IsCompact (A : Set ((BigFppfOver.toScheme B S hS).obj T))) :
    propertyUpToIso B S hS X P
      (representableOpenSubobject B S hS T A).toFunctor
      ((representableOpenSubobject B S hS T A).ι ≫ g) := by
  classical
  let Q (U : ((BigFppfOver.toScheme B S hS).obj T).Opens) :=
    propertyUpToIso B S hS X P
      (representableOpenSubobject B S hS T U).toFunctor
      ((representableOpenSubobject B S hS T U).ι ≫ g)
  have hAffine : ∀ U : ((BigFppfOver.toScheme B S hS).obj T).affineOpens,
      Q (U : ((BigFppfOver.toScheme B S hS).obj T).Opens) := by
    intro U
    let R := representableOpenSubobject B S hS T (U : _)
    let e := representableOpenSubobjectIso B S hS T (U : _)
    let V := openEtaleObject B S hS X T g hg (U : _)
    have hVaff : IsAffineSpace B S hS V.1.left.1 := by
      refine ⟨siteOpenObject B S hS T (U : _), U.2, ⟨Iso.refl _⟩⟩
    intro Z eZ
    have h := propertyUpToIso_of_affine B S hS X P haff V hVaff Z
      (eZ ≪≫ e.symm)
    have he : e.symm.hom ≫ yoneda.map
        (siteOpenObjectInclusion B S hS T (U : _)) = R.ι := by
      dsimp [e, R, representableOpenSubobjectIso, representableOpenSubobject]
      simp [Subfunctor.toRange_ι]
    have hmap : (eZ ≪≫ e.symm).hom ≫
        (yoneda.map (siteOpenObjectInclusion B S hS T (U : _)) ≫ g) =
        eZ.hom ≫ R.ι ≫ g := by
      rw [Iso.trans_hom]
      calc
        (eZ.hom ≫ e.symm.hom) ≫
            yoneda.map (siteOpenObjectInclusion B S hS T (U : _)) ≫ g =
          eZ.hom ≫ (e.symm.hom ≫
            yoneda.map (siteOpenObjectInclusion B S hS T (U : _))) ≫ g := by
              simp [Category.assoc]
        _ = eZ.hom ≫ R.ι ≫ g := by rw [he]
    change P Z ((eZ ≪≫ e.symm).hom ≫
      (yoneda.map (siteOpenObjectInclusion B S hS T (U : _)) ≫ g)) at h
    rw [hmap] at h
    exact h
  have hSup : ∀ (U : ((BigFppfOver.toScheme B S hS).obj T).Opens)
      (_ : IsCompact (U : Set ((BigFppfOver.toScheme B S hS).obj T)))
      (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens),
      Q U → Q (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) →
      Q (U ⊓ (V : ((BigFppfOver.toScheme B S hS).obj T).Opens)) →
      Q (U ⊔ (V : ((BigFppfOver.toScheme B S hS).obj T).Opens)) := by
    intro U hU V hQU hQV hQUV
    let RU := representableOpenSubobject B S hS T U
    let RV := representableOpenSubobject B S hS T (V : _)
    let hRU := representableOpenSubobject_isOpen B S hS T U
    let hRV := representableOpenSubobject_isOpen B S hS T (V : _)
    obtain ⟨W, hW, hRUW, f, hWrange, hcomp, hsq⟩ :=
      open_union_square B S hS (isAlgebraicSpace_yoneda B S hS T)
        RU RV hRU hRV
    let Wobj := siteObjectOfEtaleMap B S hS X W.toFunctor hW.1
      (W.ι ≫ g) (isEtale_comp B S hS
        (etale_of_openImmersion B S hS W.ι hW.2) hg)
    let Vobj := siteObjectOfEtaleMap B S hS X RV.toFunctor hRV.1
      (RV.ι ≫ g) (isEtale_comp B S hS
        (etale_of_openImmersion B S hS RV.ι hRV.2) hg)
    let U' := Subfunctor.range (Subfunctor.homOfLe hRUW)
    have hAcompact : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    have hVcompact : CompactSpace (V : ((BigFppfOver.toScheme B S hS).obj T).Opens).toScheme :=
      isCompact_iff_compactSpace.mp V.2.isCompact
    have hRUpoints := representableOpen_pointsRange_isCompact B S hS T U hAcompact
    have hRVpoints := representableOpen_pointsRange_isCompact B S hS T (V : _) hVcompact
    let : TopologicalSpace (points B S hS (yoneda.obj T)) :=
      pointTopology B S hS (yoneda.obj T)
    have hWpoints : IsCompact
        (Set.range (pointsMap B S hS W.toFunctor W.ι)) := by
      rw [hWrange]
      exact hRUpoints.union hRVpoints
    have hWqc : IsQuasiCompactSpace B S hS W.toFunctor :=
      openSubspace_isQuasiCompact_of_compact_range B S hS
        (isAlgebraicSpace_yoneda B S hS T) W hW hWpoints
    have hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.toFunctor :=
      openSubspace_isQuasiSeparated B S hS hZ
        (isAlgebraicSpace_yoneda B S hS T) hTqs W hW
    have hU'qc : IsQuasiCompactSpace B S hS U'.toFunctor := by
      have hRUqc : IsQuasiCompactSpace B S hS RU.toFunctor :=
        representableOpenSubobject_isQuasiCompact B S hS T U hAcompact
      exact IsQuasiCompactSpace.of_iso B S hS hRUqc
        (asIso (Subfunctor.toRange (Subfunctor.homOfLe hRUW)))
    have hVaff : IsAffineSpace B S hS Vobj.1.left.1 := by
      refine ⟨siteOpenObject B S hS T (V : _), V.2, ?_⟩
      exact ⟨(representableOpenSubobjectIso B S hS T (V : _)).symm⟩
    have hQU' : propertyUpToIso B S hS X P U'.toFunctor
        (U'.ι ≫ Wobj.1.hom.hom) := by
      intro Z eZ
      let eU : RU.toFunctor ≅ U'.toFunctor :=
        asIso (Subfunctor.toRange (Subfunctor.homOfLe hRUW))
      have hrange : eU.hom ≫ U'.ι = Subfunctor.homOfLe hRUW :=
        Subfunctor.toRange_ι _
      have hinc : Subfunctor.homOfLe hRUW ≫ W.ι = RU.ι :=
        Subfunctor.homOfLe_ι hRUW
      have hinc' : eU.symm.hom ≫ RU.ι = U'.ι ≫ W.ι := by
        rw [← hinc, ← hrange]
        simp [Category.assoc]
      have h := hQU Z (eZ ≪≫ eU.symm)
      have hmap : (eZ ≪≫ eU.symm).hom ≫ (RU.ι ≫ g) =
          eZ.hom ≫ U'.ι ≫ W.ι ≫ g := by
        rw [Iso.trans_hom]
        change eZ.hom ≫ (eU.symm.hom ≫ RU.ι) ≫ g = _
        rw [hinc']
        simp [Category.assoc]
      change P Z ((eZ ≪≫ eU.symm).hom ≫ (RU.ι ≫ g)) at h
      rw [hmap] at h
      simpa [Wobj, siteObjectOfEtaleMap, Category.assoc] using h
    have hQV' : propertyUpToIso B S hS X P Vobj.1.left.1 Vobj.1.hom.hom := by
      intro Z eZ
      exact hQV Z eZ
    let eU : RU.toFunctor ≅ U'.toFunctor :=
      asIso (Subfunctor.toRange (Subfunctor.homOfLe hRUW))
    have hrange : eU.hom ≫ U'.ι = Subfunctor.homOfLe hRUW :=
      Subfunctor.toRange_ι _
    have hinc : Subfunctor.homOfLe hRUW ≫ W.ι = RU.ι :=
      Subfunctor.homOfLe_ι hRUW
    have hinc' : eU.symm.hom ≫ RU.ι = U'.ι ≫ W.ι := by
      rw [← hinc, ← hrange]
      simp [Category.assoc]
    let pb := pullback U'.ι f
    let pb' := pullback RU.ι RV.ι
    have hcond₁ : (pullback.fst U'.ι f ≫ eU.symm.hom) ≫ RU.ι =
        pullback.snd U'.ι f ≫ RV.ι := by
      change pullback.fst U'.ι f ≫ (eU.symm.hom ≫ RU.ι) = _
      calc
        pullback.fst U'.ι f ≫ (eU.symm.hom ≫ RU.ι) =
            pullback.fst U'.ι f ≫ U'.ι ≫ W.ι := by rw [hinc']
        _ = pullback.snd U'.ι f ≫ f ≫ W.ι :=
              congrArg (fun k => k ≫ W.ι) (pullback.condition (f := U'.ι) (g := f))
        _ = pullback.snd U'.ι f ≫ RV.ι := by rw [hcomp]
    let a : pb ⟶ pb' := pullback.lift
      (pullback.fst U'.ι f ≫ eU.symm.hom) (pullback.snd U'.ι f) hcond₁
    have hcond₂ :
        (pullback.fst RU.ι RV.ι ≫ Subfunctor.toRange
          (Subfunctor.homOfLe hRUW)) ≫ U'.ι =
          pullback.snd RU.ι RV.ι ≫ f := by
      apply (cancel_mono W.ι).1
      calc
        (pullback.fst RU.ι RV.ι ≫ Subfunctor.toRange
          (Subfunctor.homOfLe hRUW)) ≫ U'.ι ≫ W.ι =
            pullback.fst RU.ι RV.ι ≫ RU.ι := by
              calc
                _ = pullback.fst RU.ι RV.ι ≫
                    (Subfunctor.toRange (Subfunctor.homOfLe hRUW) ≫ U'.ι) ≫ W.ι := by
                      simp [Category.assoc]
                _ = pullback.fst RU.ι RV.ι ≫
                    (Subfunctor.homOfLe hRUW ≫ W.ι) := by
                      rw [Subfunctor.toRange_ι]
                _ = pullback.fst RU.ι RV.ι ≫ RU.ι := by rw [hinc]
        _ = pullback.snd RU.ι RV.ι ≫ RV.ι := pullback.condition
        _ = pullback.snd RU.ι RV.ι ≫ f ≫ W.ι := by rw [hcomp]
    let b : pb' ⟶ pb := pullback.lift
      (pullback.fst RU.ι RV.ι ≫ Subfunctor.toRange
        (Subfunctor.homOfLe hRUW)) (pullback.snd RU.ι RV.ι) hcond₂
    have hUinv : eU.symm.hom ≫
        Subfunctor.toRange (Subfunctor.homOfLe hRUW) = 𝟙 U'.toFunctor := by
      dsimp [eU]
      simp
    have hUinv' : Subfunctor.toRange (Subfunctor.homOfLe hRUW) ≫
        eU.symm.hom = 𝟙 RU.toFunctor := by
      dsimp [eU]
      simp
    have haFst : a ≫ pullback.fst RU.ι RV.ι =
        pullback.fst U'.ι f ≫ eU.symm.hom := by
      dsimp [a]
      exact pullback.lift_fst _ _ _
    have haSnd : a ≫ pullback.snd RU.ι RV.ι = pullback.snd U'.ι f := by
      dsimp [a]
      exact pullback.lift_snd _ _ _
    have hbFst : b ≫ pullback.fst U'.ι f =
        pullback.fst RU.ι RV.ι ≫ Subfunctor.toRange (Subfunctor.homOfLe hRUW) := by
      dsimp [b]
      exact pullback.lift_fst _ _ _
    have hbSnd : b ≫ pullback.snd U'.ι f = pullback.snd RU.ι RV.ι := by
      dsimp [b]
      exact pullback.lift_snd _ _ _
    have hab : a ≫ b = 𝟙 pb := by
      apply pullback.hom_ext
      · calc
          (a ≫ b) ≫ pullback.fst U'.ι f = a ≫ (b ≫ pullback.fst U'.ι f) := by
            simp [Category.assoc]
          _ = a ≫ (pullback.fst RU.ι RV.ι ≫
              Subfunctor.toRange (Subfunctor.homOfLe hRUW)) := by rw [hbFst]
          _ = (pullback.fst U'.ι f ≫ eU.symm.hom) ≫
              Subfunctor.toRange (Subfunctor.homOfLe hRUW) := by
            rw [← Category.assoc, haFst]
          _ = pullback.fst U'.ι f := by
            rw [Category.assoc, hUinv, Category.comp_id]
      · calc
          (a ≫ b) ≫ pullback.snd U'.ι f = a ≫ (b ≫ pullback.snd U'.ι f) := by
            simp [Category.assoc]
          _ = a ≫ pullback.snd RU.ι RV.ι := by rw [hbSnd]
          _ = pullback.snd U'.ι f := haSnd
    have hba : b ≫ a = 𝟙 pb' := by
      apply pullback.hom_ext
      · calc
          (b ≫ a) ≫ pullback.fst RU.ι RV.ι = b ≫ (a ≫ pullback.fst RU.ι RV.ι) := by
            simp [Category.assoc]
          _ = b ≫ (pullback.fst U'.ι f ≫ eU.symm.hom) := by rw [haFst]
          _ = (pullback.fst RU.ι RV.ι ≫
              Subfunctor.toRange (Subfunctor.homOfLe hRUW)) ≫ eU.symm.hom := by
            rw [← Category.assoc, hbFst]
          _ = pullback.fst RU.ι RV.ι := by
            rw [Category.assoc]
            rw [hUinv']
            simp
      · calc
          (b ≫ a) ≫ pullback.snd RU.ι RV.ι = b ≫ (a ≫ pullback.snd RU.ι RV.ι) := by
            simp [Category.assoc]
          _ = b ≫ pullback.snd U'.ι f := by rw [haSnd]
          _ = pullback.snd RU.ι RV.ι := hbSnd
    let eInf : pb' ≅ (RU ⊓ RV).toFunctor := by
      change pullback RU.ι RV.ι ≅ (RU ⊓ RV).toFunctor
      exact pullbackInfIso (C := BigFppfOver B S hS)
        (F := yoneda.obj T) RU RV
    let ePB : pb ≅ (RU ⊓ RV).toFunctor :=
      (⟨a, b, hab, hba⟩ : pb ≅ pb') ≪≫ eInf
    let RUV := representableOpenSubobject B S hS T
      (U ⊓ (V : ((BigFppfOver.toScheme B S hS).obj T).Opens))
    have hRUV : RUV = RU ⊓ RV := by
      ext A x
      change x ∈ (representableOpenSubobject B S hS T (U ⊓ (V : _))).obj A ↔
        (x ∈ (representableOpenSubobject B S hS T U).obj A ∧
          x ∈ (representableOpenSubobject B S hS T (V : _)).obj A)
      rw [mem_representableOpenSubobject_iff, mem_representableOpenSubobject_iff,
        mem_representableOpenSubobject_iff]
      exact Set.subset_inter_iff
    have hRUV_le : RUV ≤ RU ⊓ RV := le_of_eq hRUV
    have hRI_le : RU ⊓ RV ≤ RUV := le_of_eq hRUV.symm
    let eRI : RUV.toFunctor ≅ (RU ⊓ RV).toFunctor :=
      { hom := Subfunctor.homOfLe hRUV_le
        inv := Subfunctor.homOfLe hRI_le
        hom_inv_id := by ext; rfl
        inv_hom_id := by ext; rfl }
    let e : pb ≅ RUV.toFunctor := ePB ≪≫ eRI.symm
    have hInf : eInf.hom ≫ (RU ⊓ RV).ι =
        pullback.fst RU.ι RV.ι ≫ RU.ι := by
      dsimp [eInf, pullbackInfIso]
      change Subfunctor.lift _ _ ≫ (RU ⊓ RV).ι = _
      exact Subfunctor.lift_ι _ _
    have hRUVι : eRI.inv ≫ RUV.ι = (RU ⊓ RV).ι := by
      dsimp [eRI]
      exact Subfunctor.homOfLe_ι hRI_le
    have he : e.hom ≫ RUV.ι =
        pullback.fst U'.ι f ≫ U'.ι ≫ W.ι := by
      calc
        e.hom ≫ RUV.ι = ePB.hom ≫ (RU ⊓ RV).ι := by
          dsimp [e]
          simp only [Category.assoc]
          rw [hRUVι]
        _ = a ≫ (pullback.fst RU.ι RV.ι ≫ RU.ι) := by
          dsimp [ePB]
          simp only [Category.assoc]
          rw [hInf]
        _ = pullback.fst U'.ι f ≫ eU.symm.hom ≫ RU.ι := by
          rw [← Category.assoc, haFst]
          simp only [Category.assoc]
        _ = pullback.fst U'.ι f ≫ U'.ι ≫ W.ι := by
          rw [hinc']
    have hQpb : propertyUpToIso B S hS X P (pullback U'.ι f)
        (pullback.fst U'.ι f ≫ U'.ι ≫ Wobj.1.hom.hom) := by
      intro Z eZ
      have h := hQUV Z (eZ ≪≫ e)
      have hmap : (eZ ≪≫ e).hom ≫ (RUV.ι ≫ g) =
          eZ.hom ≫ pullback.fst U'.ι f ≫ U'.ι ≫ W.ι ≫ g := by
        rw [Iso.trans_hom]
        calc
          (eZ.hom ≫ e.hom) ≫ (RUV.ι ≫ g) =
              eZ.hom ≫ (e.hom ≫ RUV.ι) ≫ g := by
                simp [Category.assoc]
        _ = eZ.hom ≫ pullback.fst U'.ι f ≫ U'.ι ≫ W.ι ≫ g := by
                rw [he]
                simp [Category.assoc]
      change P Z ((eZ ≪≫ e).hom ≫ (RUV.ι ≫ g)) at h
      rw [hmap] at h
      simpa [Wobj, siteObjectOfEtaleMap, Category.assoc] using h
    have hcomp' : f ≫ Wobj.1.hom.hom = Vobj.1.hom.hom := by
      change f ≫ (W.ι ≫ g) = RV.ι ≫ g
      calc
        f ≫ (W.ι ≫ g) = (f ≫ W.ι) ≫ g := by simp [Category.assoc]
        _ = RV.ι ≫ g := by rw [hcomp]
    have hQW := propertyUpToIso_step B S hS hZ X P hstep Wobj Vobj U' f hcomp' hsq
      hWqc hWqs hU'qc hVaff hQU' hQV' hQpb
    have hWeq : W = representableOpenSubobject B S hS T (U ⊔ (V : _)) :=
      openSubspace_eq_of_pointsMap_range_eq B S hS
        (isAlgebraicSpace_yoneda B S hS T) W _ hW
        (representableOpenSubobject_isOpen B S hS T _) (hWrange.trans
          (representableOpenSubobject_sup_pointsRange B S hS T U (V : _)).symm)
    change propertyUpToIso B S hS X P W.toFunctor (W.ι ≫ g) at hQW
    rw [hWeq] at hQW
    exact hQW
  exact _root_.Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open Q
    (fun U hU => hAffine ⟨U, hU⟩) (fun U V hU hV => hSup U hU ⟨V, hV⟩) A hA

/-- Absolute quasi-separatedness transfers along an isomorphism of presheaves. -/
private theorem isQuasiSeparated_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    IsAbsolutelyQuasiSeparated B S hS hZ G := by
  let b : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let R := OverShriek.relocalizePresheafFunctor b
  change IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (R.obj G)
  exact qs_preserved_by_iso B (⊤_ Scheme.{u}) hZ (R.mapIso e) hF

/-- The subfunctor cut out by the whole representing scheme is the top subfunctor. -/
private theorem representableOpenSubobject_top
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) :
    representableOpenSubobject B S hS T ⊤ = ⊤ := by
  apply top_unique
  intro A f _
  rw [mem_representableOpenSubobject_iff]
  exact Set.subset_univ _

/-- The isomorphism-invariant form of `P` holds on a quasi-compact quasi-separated étale
object which is isomorphic to a represented presheaf. -/
private theorem propertyUpToIso_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 → P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ X.1) (hg : IsEtale B S hS g)
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (T : BigFppfOver B S hS) (e : F ≅ yoneda.obj T) :
    propertyUpToIso B S hS X P F g := by
  have hTqc := IsQuasiCompactSpace.of_iso B S hS hqc e
  have hTqs := isQuasiSeparated_of_iso B S hS hZ e hqs
  let := compactSpace_of_isQuasiCompactSpace_yonedaObj B S hS T hTqc
  let := quasiSeparatedSpace_of_isQuasiSeparated_yoneda B S hS hZ T hTqs
  have h := propertyUpToIso_on_compact_open_of_scheme B S hS hZ X P haff hstep
    T (e.inv ≫ g) (isEtale_comp B S hS
      (etale_of_iso_presheaves B S hS e.symm) hg) hTqs ⊤ isCompact_univ
  rw [representableOpenSubobject_top] at h
  intro Z eZ
  simpa [Iso.trans_hom, Category.assoc] using
    h Z (eZ ≪≫ e ≪≫ (asIso (⊤ : Subfunctor (yoneda.obj T)).ι).symm)

/-- An open subspace carrying the isomorphism-invariant form of `P` can be enlarged by the
image of an affine open of an étale scheme neighbourhood of the complement. -/
theorem propertyUpToIso_extend_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 → P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (g : F ⟶ X.1) (hg : IsEtale B S hS g)
    (T : BigFppfOver B S hS)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))
    (U : Subfunctor F) (f : yoneda.obj T ⟶ F)
    (hsq : IsElementaryDistinguishedSquare B S hS hF U f)
    (C : Subfunctor F) (hC : IsOpenSubspace B S hS C)
    (hUC : U ≤ C) (hCqc : IsQuasiCompactSpace B S hS C.toFunctor)
    (hQC : propertyUpToIso B S hS X P C.toFunctor (C.ι ≫ g))
    (A : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    ∃ (D : Subfunctor F) (_hD : IsOpenSubspace B S hS D),
      C ≤ D ∧ IsQuasiCompactSpace B S hS D.toFunctor ∧
      propertyUpToIso B S hS X P D.toFunctor (D.ι ≫ g) ∧
      Set.range (pointsMap B S hS D.toFunctor D.ι) =
        Set.range (pointsMap B S hS C.toFunctor C.ι) ∪
        Set.range (pointsMap B S hS
          (representableOpenSubobject B S hS T A).toFunctor
          ((representableOpenSubobject B S hS T A).ι ≫ f)) := by
  let R := representableOpenSubobject B S hS T A
  have hR := representableOpenSubobject_isOpen B S hS T A
  have hRqc := representableOpenSubobject_isQuasiCompact B S hS T A
    (isCompact_iff_compactSpace.mp A.2.isCompact)
  have hRqs := representableOpenSubobject_isQuasiSeparated B S hS hZ T hTqs A
  obtain ⟨D, hD, hCD, f', hrange, hcomm, hsq'⟩ :=
    isElementaryDistinguishedSquare_openRestriction
      B S hS hF U f hsq R hR C hC hUC
  have hDqc : IsQuasiCompactSpace B S hS D.toFunctor := by
    let := pointTopology B S hS F
    apply openSubspace_isQuasiCompact_of_compact_range B S hS hF D hD
    rw [hrange]
    exact (pointsRange_isCompact B S hS hC.1 hF C.ι hCqc).union
      (pointsRange_isCompact B S hS hR.1 hF (R.ι ≫ f) hRqc)
  have hDqs := openSubspace_isQuasiSeparated B S hS hZ hF hFqs D hD
  let Wobj := siteObjectOfEtaleMap B S hS X D.toFunctor hD.1 (D.ι ≫ g)
    (isEtale_comp B S hS (etale_of_openImmersion B S hS D.ι hD.2) hg)
  let Vobj := siteObjectOfEtaleMap B S hS X R.toFunctor hR.1 (f' ≫ Wobj.1.hom.hom)
    (isEtale_comp B S hS hsq'.isEtale Wobj.2)
  let C' := Subfunctor.range (Subfunctor.homOfLe hCD)
  let eC : C.toFunctor ≅ C'.toFunctor := asIso (Subfunctor.toRange (Subfunctor.homOfLe hCD))
  have hC'qc := IsQuasiCompactSpace.of_iso B S hS hCqc eC
  have hC'qs := openSubspace_isQuasiSeparated B S hS hZ hD.1 hDqs C' hsq'.isOpenSubspace
  have hQC' : propertyUpToIso B S hS X P C'.toFunctor (C'.ι ≫ Wobj.1.hom.hom) := by
    intro Z eZ
    have hinc : eC.inv ≫ C.ι = C'.ι ≫ D.ι := by
      rw [← Subfunctor.homOfLe_ι hCD, ← Subfunctor.toRange_ι (Subfunctor.homOfLe hCD)]
      change ((eC.inv ≫ eC.hom) ≫ C'.ι) ≫ D.ι = C'.ι ≫ D.ι
      rw [eC.inv_hom_id, Category.id_comp]
    have hinc' : eC.inv ≫ C.ι ≫ g = C'.ι ≫ D.ι ≫ g := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ g) hinc
    have h := hQC Z (eZ ≪≫ eC.symm)
    change P Z (eZ.hom ≫ C'.ι ≫ D.ι ≫ g)
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hinc'] using h
  have hVaff : IsAffineSpace B S hS Vobj.1.left.1 :=
    ⟨siteOpenObject B S hS T A, A.2, ⟨(representableOpenSubobjectIso B S hS T A).symm⟩⟩
  have hQV := propertyUpToIso_of_affine B S hS X P haff Vobj hVaff
  have hpbqc := isQuasiCompactSpace_pullback
    B S hS hZ C'.ι f' hsq'.isOpenSubspace.1 hD.1 hC'qc hRqc hDqs
  have hpbqs := isAbsolutelyQuasiSeparated_pullback
    B S hS hZ C'.ι f' hsq'.isOpenSubspace.1 hR.1 hD.1 hC'qs hRqs
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  have hpbopen : IsOpenImmersion B S hS (pullback.snd C'.ι f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback C'.ι f') hsq'.isOpenSubspace.2
  let eR := (representableOpenSubobjectIso B S hS T A).symm
  have hopen : Q.presheaf (pullback.snd C'.ι f' ≫ eR.hom) :=
    MorphismProperty.RespectsIso.postcomp Q.presheaf eR.hom (pullback.snd C'.ι f') hpbopen
  obtain ⟨L, l, k, hk⟩ := hopen.1 (𝟙 _)
  have : IsIso k := hk.isIso_fst_of_isIso
  have het : IsEtale B S hS
      (pullback.fst C'.ι f' ≫ C'.ι ≫ Wobj.1.hom.hom) := by
    change IsEtale B S hS
      (pullback.fst C'.ι f' ≫ C'.ι ≫ D.ι ≫ g)
    rw [pullback.condition_assoc]
    exact isEtale_comp B S hS
      (etale_of_openImmersion B S hS (pullback.snd C'.ι f') hpbopen) Vobj.2
  have hQpb := propertyUpToIso_of_representable B S hS hZ X P haff hstep _ het
    hpbqc hpbqs L (asIso k).symm
  refine ⟨D, hD, hCD, hDqc, ?_, hrange⟩
  exact propertyUpToIso_step B S hS hZ X P hstep Wobj Vobj C' f' rfl hsq'
    hDqc hDqs hC'qc hVaff hQC' hQV hQpb

end AlgebraicGeometry.Space

end
