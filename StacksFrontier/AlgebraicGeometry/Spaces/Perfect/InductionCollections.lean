module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits

/-!
# Collections supporting the induction principle for algebraic spaces

The induction principle of Stacks 08GQ runs inside a collection `𝓑` of objects of the
spaces-étale site of a quasi-compact quasi-separated algebraic space `X` which consists of
quasi-compact quasi-separated objects, is closed under quasi-compact open subspaces, and
contains every affine object. This file exhibits the three collections of Stacks 08GR.

## Main definitions

* `AlgebraicGeometry.Space.IsQuasiCompactSeparated`: the quasi-compact separated objects.
* `AlgebraicGeometry.Space.IsQuasiCompactWithAffineDiagonal`: the quasi-compact objects with
  affine absolute diagonal.
* `AlgebraicGeometry.Space.IsBasicEtaleObject`: the quasi-compact open subspaces of `X`
  together with the quasi-compact opens of affine objects.
* `AlgebraicGeometry.Space.IsAdmissibleCollection`: the conditions a collection must satisfy
  to support the induction principle, together with membership of `X`.

## Main results

Each of the three collections contains `X`, consists of quasi-separated objects, is closed
under quasi-compact open subspaces, and contains every affine object; for the first this
specialises the collection induction principle to
`AlgebraicGeometry.Space.qcqs_induction_on_quasiCompactSeparated`, and the third is the
smallest such collection, by
`AlgebraicGeometry.Space.IsAdmissibleCollection.mem_of_isBasicEtaleObject`.

## References

* [Stacks Project, Tag 08GR](https://stacks.math.columbia.edu/tag/08GR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_inductionCollections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_inductionCollections
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Products indexed by `Type` of presheaves on the big fppf site (instance search times out
without this shortcut). -/
private instance (priority := high) hasProducts_presheaf_inductionCollections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasProducts.{0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Finite products of presheaves on the big fppf site (instance search times out without
this shortcut). -/
private instance hasFiniteProducts_presheaf_inductionCollections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasFiniteProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Binary products of presheaves on the big fppf site (instance search times out without
this shortcut). -/
private instance hasBinaryProducts_presheaf_inductionCollections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasBinaryProduct_presheaf_inductionCollections
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasLimit (pair X Y) :=
  HasLimitsOfShape.has_limit _


private noncomputable def relocalizedYonedaRepresentableBy'
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (U : BigFppfOver B S hS) :
    ((OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj U)).RepresentableBy
      (Over.mk (U.hom ≫ g)) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun x => ⟨⟨x.left ≫ U.hom, Over.homMk x.left rfl⟩, by
          change x.left ≫ U.hom ≫ g = W.hom
          simpa [Category.assoc] using x.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          calc
            x.1.2.left ≫ U.hom ≫ g = x.1.1 ≫ g :=
              congrArg (fun t => t ≫ g) x.1.2.w
            _ = W.hom := x.2)
        left_inv := fun x => by ext; rfl
        right_inv := by
          rintro ⟨⟨ψ, x⟩, hψ⟩
          apply Subtype.ext
          apply Sigma.ext
          · simp
          · dsimp
            let xInv : Over.mk ψ ⟶ U := Over.homMk x.left x.w
            let xL : (Over.mk ψ).left ⟶ U.left := Over.Hom.left xInv
            let x' : Over.mk (xL ≫ U.hom) ⟶ U := Over.homMk xL rfl
            have hidx : xL ≫ U.hom = ψ := by simp [xL]
            have hObj : Over.mk (xL ≫ U.hom) = Over.mk ψ := congrArg Over.mk hidx
            have hleft : (eqToHom hObj.symm).left = 𝟙 ((Over.mk ψ).left) := by
              rw [Over.eqToHom_left]
              rfl
            have hx : eqToHom hObj.symm ≫ x' = x := by
              apply Over.OverMorphism.ext
              rw [Over.comp_left, hleft, Category.id_comp]
              change xL = Over.Hom.left x
              rfl
            simpa [Over.homMk, x', xL, xInv] using
              (eqToHom_comp_heq x' hObj.symm).symm.trans (heq_of_eq hx) }
  · intro W W' h x
    rfl

private theorem isSeparatedOver_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (hF : IsSeparatedOver B S hS F) :
    IsSeparatedOver B S hS G := by
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  change Q (diag F) at hF
  show Q (diag G)
  have hnat : diag F ≫ prod.map e.hom e.hom = e.hom ≫ diag G := by
    apply prod.hom_ext <;> simp
  rw [← MorphismProperty.cancel_left_of_respectsIso Q e.hom, ← hnat]
  exact (MorphismProperty.cancel_right_of_respectsIso Q _ (prod.map e.hom e.hom)).2 hF

/-- The absolute diagonal of an affine scheme representative is closed. -/
private theorem isSeparated_yoneda_affine
    (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hT : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T)) :
    IsSeparatedOver B (⊤_ Scheme.{u}) hZ (yoneda.obj T) := by
  let T₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    Over.mk (𝟙 (B.obj hZ))
  have hT₀ : IsTerminal T₀ := Over.mkIdTerminal
  have hYonedaT₀ : IsTerminal (yoneda.obj T₀) := hT₀.isTerminalObj yoneda _
  let : IsTerminal (yoneda.obj T₀) := hYonedaT₀
  let f : T ⟶ T₀ := Over.homMk T.hom rfl
  have hf : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map f) := by
    let : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T) := hT
    infer_instance
  have hrel : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map f) :=
    (isSeparated_yoneda_map_iff
      B (⊤_ Scheme.{u}) hZ f).2 hf
  change IsClosedImmersion B (⊤_ Scheme.{u}) hZ
    (pullback.diagonal (yoneda.map f)) at hrel
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))
  change Q (pullback.diagonal (yoneda.map f)) at hrel
  have hpb : IsPullback prod.fst prod.snd (yoneda.map f) (yoneda.map f) := by
    convert IsPullback.of_is_product' (prodIsProd (yoneda.obj T) (yoneda.obj T))
      hYonedaT₀ using 1 <;> exact hYonedaT₀.hom_ext _ _
  let e : pullback (yoneda.map f) (yoneda.map f) ≅
      yoneda.obj T ⨯ yoneda.obj T := hpb.isoPullback.symm
  let : IsIso e.hom := e.isIso_hom
  have he : pullback.diagonal (yoneda.map f) ≫ e.hom = diag (yoneda.obj T) := by
    apply prod.hom_ext <;> simp [e, Category.assoc]
  change Q (diag (yoneda.obj T))
  rw [← he]
  exact (MorphismProperty.cancel_right_of_respectsIso Q _ e.hom).2 hrel

/-- An affine algebraic space is separated: its representing affine scheme is separated over
`Spec ℤ`. -/
private theorem isAbsolutelySeparated_of_isAffineSpace_aux
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAffineSpace B S hS F) :
    IsAbsolutelySeparated B S hS hZ F := by
  obtain ⟨T, hTaff, ⟨e⟩⟩ := hF
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let Tz : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (T.hom ≫ g)
  have hTz : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Tz) := hTaff
  have hRepSep := isSeparated_yoneda_affine B hZ Tz hTz
  let R := OverShriek.relocalizePresheafFunctor g
  have eReloc : (R.obj (yoneda.obj T)) ≅ yoneda.obj Tz :=
    (relocalizedYonedaRepresentableBy' B S (⊤_ Scheme.{u}) hS hZ g T).toIso.symm
  exact isSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ (R.mapIso e).symm
    (isSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ eReloc.symm hRepSep)

/-- The quasi-compact separated algebraic spaces in the spaces-étale site. -/
@[stacks 08GR "separated_objects"]
public abbrev IsQuasiCompactSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsQuasiCompactSpace B S hS Y ∧
    IsAbsolutelySeparated B S hS hZ Y

/-- The base algebraic space belongs to the collection. -/
@[stacks 08GR "separated_objects"]
public theorem isQuasiCompactSeparated_base
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXsep : IsAbsolutelySeparated B S hS hZ X.1) :
    IsQuasiCompactSeparated B S hS hZ X.1 := ⟨hXqc, hXsep⟩

/-- Every member of the collection is quasi-separated. -/
@[stacks 08GR "separated_objects"]
public theorem IsQuasiCompactSeparated.isAbsolutelyQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsQuasiCompactSeparated B S hS hZ Y) :
    IsAbsolutelyQuasiSeparated B S hS hZ Y :=
  isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ Y hY.2

/-- A quasi-compact open subspace of a member is again a member. -/
@[stacks 08GR "separated_objects"]
public theorem IsQuasiCompactSeparated.of_openImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i : U ⟶ W.1.left.1)
    (hW : IsQuasiCompactSeparated B S hS hZ W.1.left.1)
    (hUspace : IsAlgebraicSpace B S hS U)
    (hi : IsOpenImmersion B S hS i)
    (hUqc : IsQuasiCompactSpace B S hS U) :
    IsQuasiCompactSeparated B S hS hZ U := by
  refine ⟨hUqc, ?_⟩
  have hiSep : IsSeparated B S hS i :=
    (isSeparated_iff_presheaf
      B S hS i hUspace W.1.left.property hi.1).2 (by
      refine ⟨hi.1, ?_⟩
      intro T V g fst snd hs
      have hopen := hi.2 g fst snd hs
      show _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map snd)
      let : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map snd) := hopen
      infer_instance)
  exact isAbsolutelySeparated_of_isSeparated B S hS hZ hW.2 hiSep

/-- Every affine object of the spaces-étale site belongs to the collection. -/
@[stacks 08GR "separated_objects"]
public theorem isQuasiCompactSeparated_of_isAffineSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X)
    (hV : IsAffineSpace B S hS V.1.left.1) :
    IsQuasiCompactSeparated B S hS hZ V.1.left.1 :=
  ⟨hV.isQuasiCompactSpace,
    isAbsolutelySeparated_of_isAffineSpace_aux B S hS hZ V.1.left.1 hV⟩

/-- Induction on quasi-compact separated objects of the spaces-étale site. -/
@[stacks 08GR "separated_objects"]
public theorem qcqs_induction_on_quasiCompactSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXsep : IsAbsolutelySeparated B S hS hZ X.1)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (hPaff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      (f ≫ W.1.hom.hom = V.1.hom.hom) →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom) :
    ∀ W : SpacesEtale B S hS X,
      IsQuasiCompactSeparated B S hS hZ W.1.left.1 →
        P W.1.left.1 W.1.hom.hom :=
  qcqs_induction_on_collection B S hS hZ X hXqc
    (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ X.1 hXsep)
    (fun Y _ => IsQuasiCompactSeparated B S hS hZ Y) P
    (fun W hW => ⟨hW.1, IsQuasiCompactSeparated.isAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 hW⟩)
    (fun W U i hW hUspace hi hUqc =>
      IsQuasiCompactSeparated.of_openImmersion B S hS hZ X W U i hW hUspace hi hUqc)
    (isQuasiCompactSeparated_of_isAffineSpace B S hS hZ X) hPaff hstep

private alias mono_of_isOpenImmersion' := mono_of_isOpenImmersion

private lemma mono_relocalize_map
    {C : Type*} [Category.{u} C] {U V : C} (f : V ⟶ U)
    {F G : (Over V)ᵒᵖ ⥤ Type u} (i : F ⟶ G) [Mono i] :
    Mono ((OverShriek.relocalizePresheafFunctor f).map i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [CategoryTheory.mono_iff_injective]
  rintro ⟨⟨a, x⟩, ha⟩ ⟨⟨b, y⟩, hb⟩ h
  have hab : a = b := congrArg (fun z => z.val.fst) h
  subst b
  have hxy : i.app (Opposite.op (Over.mk a)) x =
      i.app (Opposite.op (Over.mk a)) y :=
    eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  have hxy' : x = y := (CategoryTheory.mono_iff_injective (i.app _)).1 inferInstance hxy
  subst y; rfl

private lemma affineDiagonal_of_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : F ⟶ G) [Mono i]
    (hG : IsAffineHom B S hS (diag G)) :
    IsAffineHom B S hS (diag F) := by
  intro Z g
  let g₁ := g ≫ prod.fst
  let g₂ := g ≫ prod.snd
  let gG := prod.lift (g₁ ≫ i) (g₂ ≫ i)
  obtain ⟨P, p, q, hpb⟩ := hG Z gG
  have hp₁ : p = yoneda.map q ≫ g₁ ≫ i := by
    simpa [gG, g₁, g₂, Category.assoc] using
      congrArg (fun k => k ≫ prod.fst) hpb.w
  have hp₂ : p = yoneda.map q ≫ g₂ ≫ i := by
    simpa [gG, g₁, g₂, Category.assoc] using
      congrArg (fun k => k ≫ prod.snd) hpb.w
  have hEq : yoneda.map q ≫ g₁ = yoneda.map q ≫ g₂ :=
    (cancel_mono i).1 (hp₁.symm.trans hp₂)
  let p' := yoneda.map q ≫ g₁
  have hcomm : p' ≫ diag F = yoneda.map q ≫ g := by
    apply prod.hom_ext
    · simp [p', g₁]
    · simp [p', g₂, hEq]
  have hlim : IsLimit (PullbackCone.mk p' (yoneda.map q) hcomm) := by
    have hs₁ (s : PullbackCone (diag F) g) : s.fst = s.snd ≫ g₁ := by
      simpa [g₁] using congrArg (fun k => k ≫ prod.fst) s.condition
    have hs₂ (s : PullbackCone (diag F) g) : s.fst = s.snd ≫ g₂ := by
      simpa [g₂] using congrArg (fun k => k ≫ prod.snd) s.condition
    have hcone (s : PullbackCone (diag F) g) :
        (s.fst ≫ i) ≫ diag G = s.snd ≫ gG := by
      apply prod.hom_ext
      · simpa [gG, Category.assoc] using congrArg (fun k => k ≫ i) (hs₁ s)
      · simpa [gG, Category.assoc] using congrArg (fun k => k ≫ i) (hs₂ s)
    let lift (s : PullbackCone (diag F) g) := hpb.lift (s.fst ≫ i) s.snd (hcone s)
    refine PullbackCone.IsLimit.mk hcomm lift ?_ ?_ ?_
    · intro s
      apply (cancel_mono i).1
      calc
        (lift s ≫ p') ≫ i = lift s ≫ p := by rw [hp₁]; simp [p']
        _ = s.fst ≫ i := hpb.lift_fst _ _ _
    · intro s; exact hpb.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply hpb.hom_ext
      · calc
          m ≫ p = (m ≫ p') ≫ i := by rw [hp₁]; simp [p', Category.assoc]
          _ = s.fst ≫ i := by rw [hm₁]
          _ = lift s ≫ p := (hpb.lift_fst _ _ _).symm
      · calc
          m ≫ yoneda.map q = s.snd := hm₂
          _ = lift s ≫ yoneda.map q := by rw [hpb.lift_snd]
  exact ⟨P, p', q, IsPullback.of_isLimit hlim⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- A quasi-compact algebraic space with affine absolute diagonal. -/
@[stacks 08GR "affine_diagonal_objects"]
public abbrev IsQuasiCompactWithAffineDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsQuasiCompactSpace B S hS Y ∧
    IsAffineHom B (⊤_ Scheme.{u}) hZ
      (diag (viewOverIntegers B S hS hZ Y))

set_option synthInstance.maxHeartbeats 400000 in
/-- The base algebraic space belongs to the collection. -/
@[stacks 08GR "affine_diagonal_objects"]
public theorem isQuasiCompactWithAffineDiagonal_base
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ
      (diag (viewOverIntegers B S hS hZ X.1))) :
    IsQuasiCompactWithAffineDiagonal B S hS hZ X.1 := ⟨hXqc, hXdiag⟩

/-- Every member of the collection is quasi-separated. -/
@[stacks 08GR "affine_diagonal_objects"]
public theorem IsQuasiCompactWithAffineDiagonal.isAbsolutelyQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X)
    (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1.left.1) :
    IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 := by
  apply (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ
    W.1.left.1 W.1.left.2).2
  intro U V f g hU hV
  have hf : IsAffineHom B S hS f :=
    isAffineHom_of_affine_source_of_isAffineHom_diag B S hS hZ ⟨U, hU⟩ f hW.2
  obtain ⟨T, p, q, hpb⟩ := hf ⟨V, hV⟩ g
  let T₀ := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj T
  let e : yoneda.obj T₀ ≅ pullback f g :=
    hpb.isoIsPullback _ _ (IsPullback.of_hasPullback f g)
  exact ⟨T₀, @AlgebraicGeometry.Scheme.compactSpace_of_isAffine _ T.property, ⟨e⟩⟩

/-- A quasi-compact open subspace of a member is again a member. -/
@[stacks 08GR "affine_diagonal_objects"]
public theorem IsQuasiCompactWithAffineDiagonal.of_openImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i : U ⟶ W.1.left.1)
    (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1.left.1)
    (_hUspace : IsAlgebraicSpace B S hS U)
    (hi : IsOpenImmersion B S hS i)
    (hUqc : IsQuasiCompactSpace B S hS U) :
    IsQuasiCompactWithAffineDiagonal B S hS hZ U := by
  refine ⟨hUqc, ?_⟩
  let : Mono i := mono_of_isOpenImmersion' B S hS i hi
  let f : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let j := (OverShriek.relocalizePresheafFunctor f).map i
  let : Mono j := mono_relocalize_map f i
  exact affineDiagonal_of_mono B (⊤_ Scheme.{u}) hZ j hW.2

/-- Every affine object of the spaces-étale site belongs to the collection. -/
@[stacks 08GR "affine_diagonal_objects"]
public theorem isQuasiCompactWithAffineDiagonal_of_isAffineSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X)
    (hV : IsAffineSpace B S hS V.1.left.1) :
    IsQuasiCompactWithAffineDiagonal B S hS hZ V.1.left.1 := by
  obtain ⟨hqc, hsep⟩ := isQuasiCompactSeparated_of_isAffineSpace B S hS hZ X V hV
  exact ⟨hqc, isAffineHom_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ _ hsep⟩


private alias isQuasiCompactSpace_of_iso_aux := isQuasiCompactSpace_of_iso

private theorem isAbsolutelyQuasiSeparated_of_openImmersion_aux
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (hGqs : IsAbsolutelyQuasiSeparated B S hS hZ G)
    (f : F ⟶ G) (hf : IsOpenImmersion B S hS f) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  have hmono : Mono f := mono_of_isOpenImmersion' B S hS f hf
  have : IsIso (pullback.diagonal f) := (pullback.isIso_diagonal_iff f).2 hmono
  have hdiag : IsQuasiCompact B S hS (pullback.diagonal f) := by
    intro Z hZ' hZqc g
    let e : pullback g (pullback.diagonal f) ≅ Z := asIso (pullback.fst g (pullback.diagonal f))
    exact isQuasiCompactSpace_of_iso_aux B S hS e.symm hZqc
  have hfqs : IsQuasiSeparated B S hS f := hdiag
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hF hGqs hfqs

private theorem isAbsolutelyQuasiSeparated_of_isAffineSpace_aux
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAff : IsAffineSpace B S hS F) :
    IsAbsolutelyQuasiSeparated B S hS hZ F :=
  isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ F
    (isAbsolutelySeparated_of_isAffineSpace_aux B S hS hZ F hAff)

/-- A quasi-compact open subspace of `X` or of an affine étale object over `X`. -/
@[stacks 08GR "smallest_collection"]
public def IsBasicEtaleObject
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (g : Y ⟶ X.1) : Prop :=
  IsQuasiCompactSpace B S hS Y ∧
    (IsOpenImmersion B S hS g ∨
      ∃ V : SpacesEtale B S hS X,
        IsAffineSpace B S hS V.1.left.1 ∧
          ∃ i : Y ⟶ V.1.left.1,
            IsOpenImmersion B S hS i ∧
              i ≫ V.1.hom.hom = g)

/-- The collection hypotheses from Tag 08GQ, including membership of `X`. -/
public structure IsAdmissibleCollection
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (C : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop) : Prop where
  base_mem : C X.1 (𝟙 X.1)
  quasiCompact : ∀ W : SpacesEtale B S hS X,
    C W.1.left.1 W.1.hom.hom → IsQuasiCompactSpace B S hS W.1.left.1
  quasiSeparated : ∀ W : SpacesEtale B S hS X,
    C W.1.left.1 W.1.hom.hom →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1
  of_openImmersion : ∀ (W : SpacesEtale B S hS X)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i : U ⟶ W.1.left.1),
    C W.1.left.1 W.1.hom.hom →
    IsAlgebraicSpace B S hS U →
    IsOpenImmersion B S hS i →
    IsQuasiCompactSpace B S hS U →
    C U (i ≫ W.1.hom.hom)
  of_affine : ∀ V : SpacesEtale B S hS X,
    IsAffineSpace B S hS V.1.left.1 →
      C V.1.left.1 V.1.hom.hom

/-- The base belongs to the basic collection. -/
@[stacks 08GR "smallest_collection"]
public theorem isBasicEtaleObject_base
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    IsBasicEtaleObject B S hS X X.1 (𝟙 X.1) :=
  ⟨hXqc, Or.inl (isOpenImmersion_id B S hS X.1)⟩

/-- A basic étale object is quasi-compact. -/
@[stacks 08GR "smallest_collection"]
public theorem IsBasicEtaleObject.isQuasiCompactSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X)
    (hW : IsBasicEtaleObject B S hS X W.1.left.1 W.1.hom.hom) :
    IsQuasiCompactSpace B S hS W.1.left.1 := hW.1

/-- A basic étale object is quasi-separated when `X` is. -/
@[stacks 08GR "smallest_collection"]
public theorem IsBasicEtaleObject.isAbsolutelyQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : SpacesEtale B S hS X)
    (hW : IsBasicEtaleObject B S hS X W.1.left.1 W.1.hom.hom) :
    IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 := by
  rcases hW.2 with hopen | ⟨V, hVaff, i, hi, hcomp⟩
  · exact isAbsolutelyQuasiSeparated_of_openImmersion_aux B S hS hZ
      W.1.left.property X.property hXqs W.1.hom.hom hopen
  · exact isAbsolutelyQuasiSeparated_of_openImmersion_aux B S hS hZ
      W.1.left.property V.1.left.property
      (isAbsolutelyQuasiSeparated_of_isAffineSpace_aux B S hS hZ V.1.left.1 hVaff) i hi

/-- Quasi-compact open subspaces of basic objects are basic. -/
@[stacks 08GR "smallest_collection"]
public theorem IsBasicEtaleObject.of_openImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (W : SpacesEtale B S hS X)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i : U ⟶ W.1.left.1)
    (hW : IsBasicEtaleObject B S hS X W.1.left.1 W.1.hom.hom)
    (hUspace : IsAlgebraicSpace B S hS U)
    (hi : IsOpenImmersion B S hS i)
    (hUqc : IsQuasiCompactSpace B S hS U) :
    IsBasicEtaleObject B S hS X U (i ≫ W.1.hom.hom) := by
  refine ⟨hUqc, ?_⟩
  rcases hW.2 with hopen | ⟨V, hVaff, j, hj, hcomp⟩
  · exact Or.inl (MorphismProperty.comp_mem _ _ _ hi hopen)
  · refine Or.inr ⟨V, hVaff, i ≫ j,
      MorphismProperty.comp_mem _ _ _ hi hj, ?_⟩
    simpa [Category.assoc] using congrArg (fun k => i ≫ k) hcomp

/-- Every affine object of the étale site is basic. -/
@[stacks 08GR "smallest_collection"]
public theorem isBasicEtaleObject_of_isAffineSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X)
    (hV : IsAffineSpace B S hS V.1.left.1) :
    IsBasicEtaleObject B S hS X V.1.left.1 V.1.hom.hom := by
  let hVorig := hV
  obtain ⟨T, hTaff, ⟨e⟩⟩ := hV
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  have hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T) := by
    refine ⟨T, 𝟙 _, inferInstance, ?_, fun _ _ hg => hg⟩
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 (yoneda.obj T)), ?_⟩
    intro A D g fst snd hpb
    have hsnd : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    let : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    let : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
      Functor.map_isIso _ snd
    show Surjective ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  exact ⟨isQuasiCompactSpace_of_iso_aux B S hS e.symm hTqc, Or.inr ⟨V, hVorig, 𝟙 _,
    isOpenImmersion_id B S hS V.1.left.1, by simp⟩⟩

/-- Every admissible collection contains all basic objects. -/
@[stacks 08GR "smallest_collection"]
public theorem IsAdmissibleCollection.mem_of_isBasicEtaleObject
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (C : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (hC : IsAdmissibleCollection B S hS hZ X C)
    (W : SpacesEtale B S hS X)
    (hW : IsBasicEtaleObject B S hS X W.1.left.1 W.1.hom.hom) :
    C W.1.left.1 W.1.hom.hom := by
  rcases hW.2 with hopen | ⟨V, hVaff, i, hi, hcomp⟩
  · let Xobj := spacesTerminal B S hS X
    simpa [Xobj, spacesTerminal, Category.comp_id] using
      hC.of_openImmersion Xobj W.1.left.1 W.1.hom.hom
      hC.base_mem W.1.left.property hopen hW.1
  · simpa [hcomp] using hC.of_openImmersion V W.1.left.1 i (hC.of_affine V hVaff)
      W.1.left.property hi hW.1


end AlgebraicGeometry.Space

end
