module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gabber's theorem in degree zero

Let `(A, I)` be a henselian pair, `X = Spec A` and `i : Z = Spec (A ⧸ I) ⟶ X`. For every abelian
sheaf `F` on `X_étale` the restriction map `H⁰(X, F) → H⁰(Z, F|_Z)` is bijective. This is the
case `q = 0` of Gabber's theorem ([Stacks, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)),
and the source deduces it from [Stacks, Tag 09ZH], which is stated for sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair`.

## Implementation notes

Through `H⁰ ≅ Γ` restriction is the unit `F ⟶ i_* i⁻¹ F` on sections over the final object
(`Stacks.EtaleCohomology.equiv₀_etaleCohomologyRestrictionMap_zero`). The forgetful functor
`AddCommGrpCat ⥤ Type` carries the abelian unit to the unit for sheaves of sets, up to the
invertible comparison `Stacks.EtaleCohomology.coefficientPullbackComparison` of the two inverse
images (`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`), and on sheaves of sets the
unit on global sections is the comparison that Tag 09ZH shows to be bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- The unit of the inverse-image/direct-image adjunction for sheaves of sets on small étale
sites is the unit of the left Kan extension followed by the sheafification unit. -/
theorem smallEtaleSheafAdjunction_unit_hom {X Y : Scheme.{u}} (i : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange i)
      (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology).unit.app F).hom =
      (smallEtaleBaseChange i).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (smallEtaleBaseChange i).op
          (toSheafify Y.smallEtaleTopology ((smallEtaleBaseChange i).op.lan.obj F.obj)) :=
  rfl

/-- For a henselian pair `(A, I)` and a sheaf of sets `F` on the small étale site of `Spec A`,
the unit of `F ⟶ i_* i⁻¹ F` on sections over the final object is bijective (Tag 09ZH). -/
theorem bijective_sheafAdjunction_unit_app_terminal_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (Fs : Sheaf (Spec (.of A)).smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (fun t : Fs.obj.obj (op (terminal (Spec (.of A)).Etale)) =>
      ((Functor.sheafPullbackConstruction.sheafPullback
        (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
        (Type (u + 1)) _ (Spec (.of (A ⧸ I))).smallEtaleTopology).obj Fs).obj.map
        ((isTerminalSmallEtaleBaseChangeObj (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          terminalIsTerminal).from (terminal _)).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
          (Type (u + 1)) _ (Spec (.of (A ⧸ I))).smallEtaleTopology).unit.app Fs).hom.app
          (op (terminal _)) t)) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let G := smallEtaleBaseChange i
  let adjS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology
  let T : Z.Etale := terminal Z.Etale
  let iFs := (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology).obj Fs
  let tX' : X.Etale := terminal X.Etale
  let g : T ⟶ G.obj tX' := (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).from _
  let uS' : Fs.obj.obj (op tX') → iFs.obj.obj (op (G.obj tX')) :=
    (adjS.unit.app Fs).hom.app (op tX')
  have h09ZH := isIso_globalSectionsComparison_quotient_of_henselianPair.{u, 0} A I hI
  have hmapAt : Function.Bijective (smallEtaleGlobalSectionsMapAt.{u, 0} i g Fs) := by
    rw [← (globalSectionsSmallEtaleInverseImageComparison.{u, 0} i).property Fs g]
    exact ConcreteCategory.bijective_of_isIso _
  let ΓX := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (Type (u + 1))
    terminalIsTerminal).app Fs
  let ΓZ := (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (Type (u + 1))
    terminalIsTerminal).app iFs
  have hfac : ⇑(smallEtaleGlobalSectionsMapAt.{u, 0} i g Fs) =
      ⇑ΓZ.inv ∘ (fun t => iFs.obj.map g.op (uS' t)) ∘ ⇑ΓX.hom := by
    funext x
    change ΓZ.inv (((toSheafify Z.smallEtaleTopology
        ((smallEtaleBaseChange i).op.lan.obj Fs.obj)).app (op T))
      (((smallEtaleBaseChange i).op.lan.obj Fs.obj).map g.op
        ((((smallEtaleBaseChange i).op.lanUnit.app Fs.obj).app (op tX')) (ΓX.hom x)))) = _
    refine congrArg ΓZ.inv ?_
    have hu := ConcreteCategory.congr_hom (congrArg (fun φ => φ.app (op tX'))
      (smallEtaleSheafAdjunction_unit_hom i Fs)) (ΓX.hom x)
    have h2 := ConcreteCategory.congr_hom ((toSheafify Z.smallEtaleTopology
      ((smallEtaleBaseChange i).op.lan.obj Fs.obj)).naturality g.op)
      ((((smallEtaleBaseChange i).op.lanUnit.app Fs.obj).app (op tX')) (ΓX.hom x))
    simp only [CategoryTheory.comp_apply, NatTrans.comp_app] at h2 hu
    exact ((congrArg (iFs.obj.map g.op) hu).trans h2.symm).symm
  rw [hfac] at hmapAt
  have hX : Function.Bijective ΓX.hom := ConcreteCategory.bijective_of_isIso _
  have hZ : Function.Bijective ΓZ.inv := ConcreteCategory.bijective_of_isIso _
  exact (Function.Bijective.of_comp_iff _ hX).mp ((Function.Bijective.of_comp_iff' hZ _).mp hmapAt)

/-- For a henselian pair `(A, I)` and a sheaf of sets `F` on the small étale site of `Spec A`,
the unit of `F ⟶ i_* i⁻¹ F` on sections over `Spec A` itself is bijective (Tag 09ZH). -/
theorem bijective_sheafAdjunction_unit_app_mkId_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (Fs : Sheaf (Spec (.of A)).smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (fun s : Fs.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))) =>
      ((Functor.sheafPullbackConstruction.sheafPullback
        (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
        (Type (u + 1)) _ (Spec (.of (A ⧸ I))).smallEtaleTopology).obj Fs).obj.map
        (((isTerminalEtaleMkId _).isTerminalObj
          (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).from
          (terminal _)).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
          (Type (u + 1)) _ (Spec (.of (A ⧸ I))).smallEtaleTopology).unit.app Fs).hom.app
          (op (Scheme.Etale.mk (𝟙 _))) s)) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let G := smallEtaleBaseChange i
  let adjS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology
  let T : Z.Etale := terminal Z.Etale
  let tX : X.Etale := Scheme.Etale.mk (𝟙 X)
  let htX : IsTerminal tX := isTerminalEtaleMkId X
  let fromT : T ⟶ G.obj tX := (htX.isTerminalObj G).from T
  let iFs := (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology).obj Fs
  let tX' : X.Etale := terminal X.Etale
  let g : T ⟶ G.obj tX' := (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).from _
  let e : tX ⟶ tX' := terminal.from tX
  have he : IsIso e := isIso_of_isTerminal htX terminalIsTerminal e
  let uS : Fs.obj.obj (op tX) → iFs.obj.obj (op (G.obj tX)) := (adjS.unit.app Fs).hom.app (op tX)
  let uS' : Fs.obj.obj (op tX') → iFs.obj.obj (op (G.obj tX')) :=
    (adjS.unit.app Fs).hom.app (op tX')
  have hmid : Function.Bijective (fun t => iFs.obj.map g.op (uS' t)) :=
    bijective_sheafAdjunction_unit_app_terminal_of_henselianPair A I hI Fs
  have E2 : (fun s => iFs.obj.map fromT.op (uS s)) ∘ Fs.obj.map e.op =
      fun t => iFs.obj.map g.op (uS' t) := by
    funext t
    have hn := ConcreteCategory.congr_hom ((adjS.unit.app Fs).hom.naturality e.op) t
    change uS (Fs.obj.map e.op t) = iFs.obj.map (G.map e).op (uS' t) at hn
    change iFs.obj.map fromT.op (uS (Fs.obj.map e.op t)) = _
    rw [hn]
    change (iFs.obj.map (G.map e).op ≫ iFs.obj.map fromT.op) (uS' t) = _
    rw [← iFs.obj.map_comp, ← op_comp,
      show fromT ≫ G.map e = g from
        (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).hom_ext _ _]
  have hFe : Function.Bijective (Fs.obj.map e.op) := ConcreteCategory.bijective_of_isIso _
  rw [← E2] at hmid
  exact (Function.Bijective.of_comp_iff _ hFe).mp hmid

/-- **Gabber's theorem in degree zero.** For a henselian pair `(A, I)`, restriction
`H⁰(Spec A, F) → H⁰(Spec (A ⧸ I), F|_{Spec (A ⧸ I)})` is bijective for every abelian sheaf `F`
on the small étale site of `Spec A`. -/
@[sga "4 XII 6.13" "partial"]
theorem bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F 0) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let G := smallEtaleBaseChange i
  let U := forget AddCommGrpCat.{u + 1}
  let Fs : Sheaf X.smallEtaleTopology (Type (u + 1)) := (sheafCompose X.smallEtaleTopology U).obj F
  let adjS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology
  let adjA := etaleAbelianInverseImageDirectImageAdj.{u, 0} i
  let T : Z.Etale := terminal Z.Etale
  let hT : IsTerminal T := terminalIsTerminal
  let tX : X.Etale := Scheme.Etale.mk (𝟙 X)
  let htX : IsTerminal tX := isTerminalEtaleMkId X
  let fromT : T ⟶ G.obj tX := (htX.isTerminalObj G).from T
  let iFs := (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1))
    X.smallEtaleTopology Z.smallEtaleTopology).obj Fs
  let uS : Fs.obj.obj (op tX) → iFs.obj.obj (op (G.obj tX)) := (adjS.unit.app Fs).hom.app (op tX)
  -- The sets-valued statement: Tag 09ZH.
  have hsets : Function.Bijective (fun s => iFs.obj.map fromT.op (uS s)) :=
    bijective_sheafAdjunction_unit_app_mkId_of_henselianPair A I hI Fs
  -- Transport to abelian groups along the comparison of the two inverse images.
  have : (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions G.op :=
    preservesLeftKanExtensions_forget_smallEtaleBaseChange i
  let cmp := coefficientPullbackComparison G X.smallEtaleTopology Z.smallEtaleTopology U F
  have hcmp : IsIso cmp := by
    rw [show cmp = _ from (coefficientPullbackTwoSquare_app G _ _ U F).symm]
    infer_instance
  have hunit := coefficientPullbackComparison_unit G X.smallEtaleTopology Z.smallEtaleTopology U F
  have hcT : Function.Bijective (cmp.hom.app (op T)) := ConcreteCategory.bijective_of_isIso _
  have key : (cmp.hom.app (op T)) ∘ (fun s => iFs.obj.map fromT.op (uS s)) =
      (fun s : F.obj.obj (op tX) =>
        ((etaleAbelianInverseImage.{u, 0} i).obj F).obj.map fromT.op
          (((adjA.unit.app F).hom.app (op tX)) s)) := by
    funext s
    have hc := ConcreteCategory.congr_hom (cmp.hom.naturality fromT.op) (uS s)
    have hu := ConcreteCategory.congr_hom (congrArg (fun φ : Fs ⟶
      (G.sheafPushforwardContinuous (Type (u + 1)) X.smallEtaleTopology
        Z.smallEtaleTopology).obj ((sheafCompose Z.smallEtaleTopology U).obj
          ((etaleAbelianInverseImage.{u, 0} i).obj F)) => φ.hom.app (op tX)) hunit) s
    simp only [CategoryTheory.comp_apply] at hc hu
    exact hc.trans (congrArg _ hu)
  have hab := key ▸ hcT.comp hsets
  let eX := Sheaf.H.equiv₀ F htX
  let eZ := Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, 0} i).obj F) hT
  have hfun : (fun x => eZ (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0 x)) =
      (fun x => ((etaleAbelianInverseImage.{u, 0} i).obj F).obj.map fromT.op
        (((adjA.unit.app F).hom.app (op tX)) (eX x))) :=
    funext fun x => equiv₀_etaleCohomologyRestrictionMap_zero.{u, 0, u + 1} i F hT x
  exact (Function.Bijective.of_comp_iff' eZ.bijective _).mp (hfun ▸ hab.comp eX.bijective :
    Function.Bijective fun x => eZ (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0 x))

end Stacks.EtaleCohomology
