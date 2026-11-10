module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroAdjunctionAnyUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero and the underlying abelian sheaf, at independent universes

Let `(C, J)` be a site, `R` a sheaf of rings on it and `U` an object of `C`.  The left Kan
extension along `(Over.forget U).op` is, over `V`, the coproduct of the values at the objects
`φ : V ⟶ U` of `C/U` (Stacks 0F4K), and extension by zero of sheaves of modules commutes with
forgetting the module structure (Stacks 08P4).

This file proves both with the universes of the site `C : Type u₁`, of its morphisms
`Category.{v₁} C`, of the sheaf of rings `RingCat.{w}` and of the module sections mutually
independent, related only by `UnivLE`.  The single-universe statements of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroExactness.lean` are their
specializations.

## Main definitions

* `Stacks.Sites.ExtensionByZero.AnyUniverse.extensionByZeroCompToSheafIso`: extension by zero
  commutes with forgetting the module structure.

## Main results

* `Stacks.Sites.ExtensionByZero.AnyUniverse.isIso_lanSigmaDesc`: the left Kan extension along
  `(Over.forget U).op` is computed by direct sums.

## Implementation notes

`UnivLE.{w, v}`, `UnivLE.{u₁, v}` and `UnivLE.{v₁, v}` make the presheaf-level extension by
zero exist, through `Stacks.Sites.ExtensionByZero.presheafRestrictionIsRightAdjoint_of_univLE`;
`UnivLE.{max u₁ v₁, v}` gives the colimits of shape `CostructuredArrow (Over.forget U).op (op V)`
by which the left Kan extension is computed.  Neither it nor the pair `UnivLE.{u₁, v}`,
`UnivLE.{v₁, v}` implies the other by instance search, which is why all four are carried.

## References

* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 08P4](https://stacks.math.columbia.edu/tag/08P4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.AnyUniverse

universe v w u₁ v₁ m

section LeftKanExtension

/-- Precomposing the inclusion of the summand at `a` with the transport along `a = b` gives the
inclusion of the summand at `b`. -/
lemma map_op_eqToHom_comp_sigmaι {C : Type u₁} [Category.{v₁} C] {U V : C} {D : Type*}
    [Category D] (F : (Over U)ᵒᵖ ⥤ D) [HasCoproduct fun φ : V ⟶ U => F.obj (op (Over.mk φ))]
    {a b : V ⟶ U} (h : a = b) :
    F.map (op (eqToHom (congrArg Over.mk h))) ≫
        Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) a =
      Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) b := by
  subst h
  exact (congrArg (· ≫ _) (F.map_id _)).trans (Category.id_comp _)

/-- The left Kan extension along `(Over.forget U).op` is, over `V`, the
coproduct of the values of `F` at the objects `φ : V ⟶ U` of `C/U`, the comparison map being
the one induced by the Kan extension unit on each summand. Applied to the small étale site of
a scheme and an étale `U ⟶ X`, this is the presheaf extension by zero along `U ⟶ X`: its
sections over `V` are the direct sum of the sections of `F` over the lifts `V ⟶ U`. -/
theorem isIso_lanSigmaDesc
    {C : Type u₁} [Category.{v₁} C] (U : C)
    [UnivLE.{u₁, m}] [UnivLE.{v₁, m}] [UnivLE.{max u₁ v₁, m}]
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{m}, (Over.forget U).op.HasLeftKanExtension F]
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{m}) (V : C) :
    IsIso (Sigma.desc
      (f := fun φ : V ⟶ U => F.obj (op (Over.mk φ)))
      (P := (((Over.forget U).op.lan.obj F).obj (op V)))
      (fun φ => (((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ))))) := by
  classical
  let L := (Over.forget U).op
  let J := CostructuredArrow L (op V)
  let G := CostructuredArrow.proj L (op V) ⋙ F
  let ix (j : J) : V ⟶ U := j.hom.unop ≫ j.left.unop.hom
  let k (j : J) : Over.mk (ix j) ⟶ j.left.unop := Over.homMk j.hom.unop (by rfl)
  let terminal (φ : V ⟶ U) : J :=
    CostructuredArrow.mk (S := L) (T := op V) (Y := op (Over.mk φ)) (𝟙 (op V))
  let eta (j : J) : j ⟶ terminal (ix j) :=
    CostructuredArrow.homMk (k j).op (by simp [L, terminal, k])
  let c : Cocone G := Cocone.mk (∐ fun φ : V ⟶ U => F.obj (op (Over.mk φ))) {
    app := fun j => F.map (Opposite.op (k j)) ≫
      Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j)
    naturality := by
      intro j j' f
      change F.map f.left ≫ F.map (op (k j')) ≫
          Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j') =
        F.map (op (k j)) ≫
          Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j)
      have hrel : j'.hom.unop ≫ f.left.unop.left = j.hom.unop :=
        congrArg (fun g => g.unop) (CostructuredArrow.w f)
      have hix : ix j = ix j' := by
        simp only [ix, ← hrel, Category.assoc, Over.w]
      have hobj : Over.mk (ix j) = Over.mk (ix j') := congrArg Over.mk hix
      have hmor : eqToHom hobj ≫ k j' ≫ f.left.unop = k j := by
        apply Over.OverMorphism.ext
        change (eqToHom hobj).left ≫ j'.hom.unop ≫ f.left.unop.left = j.hom.unop
        simpa [Category.assoc] using hrel
      have hpath : f.left ≫ op (k j') ≫ op (eqToHom hobj) = op (k j) := by
        apply Quiver.Hom.unop_inj
        change (eqToHom hobj ≫ k j') ≫ f.left.unop = k j
        simpa only [Category.assoc] using hmor
      rw [← map_op_eqToHom_comp_sigmaι F hix, ← hpath]
      simp only [Functor.map_comp, Category.assoc] }
  have hterminal (φ : V ⟶ U) :
      c.ι.app (terminal φ) = Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ := by
    have hidx : ix (terminal φ) = φ := by simp [ix, terminal]
    have hk : k (terminal φ) = eqToHom (congrArg Over.mk hidx) := by
      apply Over.OverMorphism.ext
      simp [terminal, k]
    change F.map (op (k (terminal φ))) ≫
        Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) (ix (terminal φ)) = _
    rw [hk]
    exact map_op_eqToHom_comp_sigmaι F hidx
  have hc : IsColimit c := IsColimit.mk
    (fun s => Sigma.desc fun φ => s.ι.app (terminal φ))
    (by
      intro s j
      dsimp [c]
      rw [Category.assoc, Sigma.ι_comp_desc]
      exact s.w (eta j))
    (by
      intro s m hm
      apply Sigma.hom_ext
      intro φ
      rw [Sigma.ι_comp_desc]
      simpa only [hterminal] using hm (terminal φ))
  let e₁ : (∐ fun φ : V ⟶ U => F.obj (op (Over.mk φ))) ≅ colimit G :=
    hc.coconePointUniqueUpToIso (colimit.isColimit G)
  let e₂ : (((Over.forget U).op.lan.obj F).obj (op V)) ≅ colimit G :=
    Functor.leftKanExtensionObjIsoColimit L F (op V)
  have he :
      Sigma.desc
        (f := fun φ : V ⟶ U => F.obj (op (Over.mk φ)))
        (P := (((Over.forget U).op.lan.obj F).obj (op V)))
        (fun φ => ((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ))) =
          (e₁ ≪≫ e₂.symm).hom := by
    apply Sigma.hom_ext
    intro φ
    have hunit : ((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ)) ≫ e₂.hom =
        colimit.ι G (terminal φ) :=
      Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
        (L := L) (F := F) (X := op (Over.mk φ))
    have hcolim : Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ ≫ e₁.hom =
        colimit.ι G (terminal φ) :=
      (congrArg (fun x => x ≫ e₁.hom) (hterminal φ).symm).trans
        (IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit G) (terminal φ))
    rw [Sigma.ι_comp_desc, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hcolim]
    exact (Iso.eq_comp_inv e₂).2 hunit
  rw [he]
  infer_instance

end LeftKanExtension

section ForgetModuleStructure

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{w}) (U : C)
  [UnivLE.{w, v}] [UnivLE.{u₁, v}] [UnivLE.{v₁, v}] [UnivLE.{max u₁ v₁, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v},
    (Over.forget U).op.HasLeftKanExtension F]

/-- Extension by zero commutes with forgetting the module structure: the
square formed by extension by zero for modules, extension by zero for abelian sheaves and the
two forgetful functors commutes up to natural isomorphism.

Stated with the universes of the site `C : Type u₁`, of its morphisms `Category.{v₁} C`, of the
sheaf of rings `Sheaf J RingCat.{w}` and of the module sections `SheafOfModules.{v}` mutually
independent, related only by the four `UnivLE` hypotheses of the variable block; see the
implementation notes at the top of the file for what each of them buys. At `u₁ = v₁ = w = v`
all four hold by `inferInstance`, so the single-universe form is a specialisation of this one
and no second construction exists. -/
@[sga "4 IV 11.3.1" "special case"]
noncomputable def extensionByZeroCompToSheafIso :
    SheafOfModules.pullback.{v}
        (F := Over.forget U) (S := R.over U) (R := R)
        (𝟙 (R.over U)) ⋙ SheafOfModules.toSheaf.{v} R ≅
      SheafOfModules.toSheaf.{v} (R.over U) ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Over.forget U) AddCommGrpCat.{v} (J.over U) J := by
  classical
  have := presheafRestrictionIsRightAdjoint_of_univLE.{v} J R U
  let φs : (R.over U) ⟶ (R.over U) := 𝟙 (R.over U)
  let φ : (R.over U).obj ⟶ ((Over.forget U).op ⋙ R.obj) := φs.hom
  let P := PresheafOfModules.pullback.{v} (F := Over.forget U)
    (R := R.obj) (S := (R.over U).obj) φ
  let Q := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{v} (J.over U) J
  let L := (Over.forget U).op
  let Fmod : SheafOfModules.{v} (R.over U) ⥤ PresheafOfModules.{v} R.obj :=
    SheafOfModules.forget (R.over U) ⋙ P
  let FAb : SheafOfModules.{v} (R.over U) ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
    SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.toPresheaf (R.over U).obj
  let Lpre := (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{v}).obj L
  let Fpres := Fmod ⋙ PresheafOfModules.toPresheaf R.obj
  let unitMod := PresheafOfModules.pullbackPushforwardAdjunction.{v} φ
  let τ := PresheafOfModules.pushforwardCompToPresheaf.{v}
    (F := Over.forget U) (R := R.obj) (S := (R.over U).obj) φ
  let η₀ : FAb ⟶ Fpres ⋙ Lpre := {
    app := fun M =>
      (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
        τ.hom.app (P.obj M.val)
    naturality := by
      intro M N f
      change (PresheafOfModules.toPresheaf (R.over U).obj).map f.val ≫
          (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app N.val) ≫
            τ.hom.app (P.obj N.val) =
        (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
          τ.hom.app (P.obj M.val) ≫
          Lpre.map ((PresheafOfModules.toPresheaf R.obj).map (P.map f.val))
      calc
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map
              (f.val ≫ unitMod.unit.app N.val) ≫ τ.hom.app (P.obj N.val) := by
            simp [Functor.map_comp, Category.assoc]
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map
              (unitMod.unit.app M.val ≫
                (PresheafOfModules.pushforward φ).map (P.map f.val)) ≫
              τ.hom.app (P.obj N.val) :=
            congrArg
              (fun g => (PresheafOfModules.toPresheaf (R.over U).obj).map g ≫
                τ.hom.app (P.obj N.val)) (unitMod.unit.naturality f.val)
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
              (PresheafOfModules.toPresheaf (R.over U).obj).map
                ((PresheafOfModules.pushforward φ).map (P.map f.val)) ≫
              τ.hom.app (P.obj N.val) := by
            simp [Functor.map_comp, Category.assoc]
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
              τ.hom.app (P.obj M.val) ≫
              Lpre.map ((PresheafOfModules.toPresheaf R.obj).map (P.map f.val)) :=
            congrArg (fun g =>
              (PresheafOfModules.toPresheaf (R.over U).obj).map
                (unitMod.unit.app M.val) ≫ g) (τ.hom.naturality (P.map f.val)) }
  let adjLan := L.lanAdjunction AddCommGrpCat.{v}
  let etaApp (M : SheafOfModules.{v} (R.over U)) :=
    (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)).symm (η₀.app M)
  let η : FAb ⋙ L.lan ⟶ Fpres := {
    app := etaApp
    naturality := by
      intro M N f
      apply (adjLan.homEquiv (FAb.obj M) (Fpres.obj N)).injective
      change (adjLan.homEquiv (FAb.obj M) (Fpres.obj N))
          (L.lan.map (FAb.map f) ≫ etaApp N) = _
      calc
        _ = FAb.map f ≫ η₀.app N := by
          rw [adjLan.homEquiv_naturality_left (FAb.map f) (etaApp N)]
          congr 1
          exact Equiv.apply_symm_apply (adjLan.homEquiv (FAb.obj N) (Fpres.obj N))
            (η₀.app N)
        _ = η₀.app M ≫ Lpre.map (Fpres.map f) := η₀.naturality f
        _ = η₀.app M ≫ L.whiskerLeft (Fpres.map f) := rfl
        _ = (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (etaApp M) ≫
              L.whiskerLeft (Fpres.map f) := by
            congr 1
            exact (Equiv.apply_symm_apply
              (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (η₀.app M)).symm
        _ = (adjLan.homEquiv (FAb.obj M) (Fpres.obj N)) (etaApp M ≫ Fpres.map f) :=
            (adjLan.homEquiv_naturality_right (etaApp M) (Fpres.map f)).symm }
  have hη (M : SheafOfModules.{v} (R.over U)) (V : C) :
      IsIso ((η.app M).app (op V)) := by
    let A : (V ⟶ U) → ModuleCat (R.obj.obj (op V)) := extensionByZeroSummands J R U M V
    let B : (V ⟶ U) → AddCommGrpCat.{v} := fun f => (FAb.obj M).obj (op (Over.mk f))
    let H := Discrete.functor A
    let forgetMod := forget₂ (ModuleCat (R.obj.obj (op V))) AddCommGrpCat
    let q := extensionByZeroPresheafSectionIso J R U M V
    let eNat : H ⋙ forgetMod ≅ Discrete.functor B :=
      Discrete.compNatIsoDiscrete A forgetMod ≪≫
        Discrete.natIso (fun i => eqToIso (show forgetMod.obj (A i.as) = B i.as from rfl))
    let e : (∐ B) ≅ forgetMod.obj (∐ A) :=
      (HasColimit.isoOfNatIso eNat).symm ≪≫ (preservesColimitIso forgetMod H).symm
    let μ : (∐ B) ⟶ (Fpres.obj M).obj (op V) := e.hom ≫ forgetMod.map q.inv
    have hμ : IsIso μ := inferInstanceAs (IsIso (e ≪≫ forgetMod.mapIso q.symm).hom)
    let d := Sigma.desc
      (f := B)
      (P := (L.lan.obj (FAb.obj M)).obj (op V))
      (fun f => ((L.lanUnit.app (FAb.obj M)).app (op (Over.mk f))))
    have hd : IsIso d := isIso_lanSigmaDesc U (FAb.obj M) V
    have hcomp : d ≫ (η.app M).app (op V) = μ := by
      apply Sigma.hom_ext
      intro f
      have hdesc : Sigma.ι B f ≫ d =
          (L.lanUnit.app (FAb.obj M)).app (op (Over.mk f)) := Sigma.ι_comp_desc _ f
      have he : Sigma.ι B f ≫ e.hom =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f) := by
        dsimp [e]
        rw [← Category.assoc, HasColimit.ι_isoOfNatIso_inv, Category.assoc,
          ι_preservesColimitIso_inv]
      have hunitMod : Sigma.ι A f ≫ q.inv =
          ((PresheafOfModules.pullbackPushforwardAdjunction.{v}
            (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
            (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
              (op (Over.mk f)) :=
        HEq.eq (extensionByZeroPresheafSectionIso_inv_ι J R U M V f)
      have hadj : ((L.lanUnit.app (FAb.obj M)).app (op (Over.mk f))) ≫
          (η.app M).app (op V) = (η₀.app M).app (op (Over.mk f)) := by
        have h' : η₀.app M = adjLan.unit.app (FAb.obj M) ≫ Lpre.map (etaApp M) := by
          calc
            η₀.app M = (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (etaApp M) :=
              (Equiv.apply_symm_apply (adjLan.homEquiv (FAb.obj M) (Fpres.obj M))
                (η₀.app M)).symm
            _ = adjLan.unit.app (FAb.obj M) ≫ Lpre.map (etaApp M) := by
              simpa [Lpre] using adjLan.homEquiv_unit (f := etaApp M)
        simpa [Lpre, η, etaApp, adjLan, Functor.lanAdjunction_unit, L] using
          congrArg (fun α => α.app (op (Over.mk f))) h'.symm
      have hη₀ : (η₀.app M).app (op (Over.mk f)) =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map
            (((PresheafOfModules.pullbackPushforwardAdjunction.{v}
              (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
              (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
                (op (Over.mk f))) := by
        apply AddCommGrpCat.ext
        intro x
        rfl
      have hRHS : Sigma.ι B f ≫ μ =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map
            (((PresheafOfModules.pullbackPushforwardAdjunction.{v}
              (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
              (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
                (op (Over.mk f))) := by
        have h3 : (eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f)) ≫
              forgetMod.map q.inv =
            eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f ≫ q.inv) := by
          rw [Category.assoc, ← Functor.map_comp]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun x => x ≫ forgetMod.map q.inv) he).trans
            (h3.trans (congrArg
              (fun x => eNat.inv.app (Discrete.mk f) ≫ forgetMod.map x) hunitMod)))
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ (η.app M).app (op V)) hdesc).trans
          (hadj.trans hη₀))).trans hRHS.symm
    have hcompIso : IsIso (d ≫ (η.app M).app (op V)) := by
      rw [hcomp]
      exact hμ
    exact IsIso.of_isIso_comp_left d ((η.app M).app (op V))
  let ηIso : FAb ⋙ L.lan ≅ Fmod ⋙ PresheafOfModules.toPresheaf R.obj :=
    NatIso.ofComponents
      (fun M => NatIso.ofComponents
        (fun V => asIso ((η.app M).app V)) (fun f => (η.app M).naturality f))
      (fun f => η.naturality f)
  exact Functor.isoWhiskerRight
      (SheafOfModules.pullbackIso.{v}
        (F := Over.forget U) (S := R.over U) (R := R) φs)
      (SheafOfModules.toSheaf R) ≪≫
    Functor.isoWhiskerRight ηIso.symm (presheafToSheaf J AddCommGrpCat.{v})

end ForgetModuleStructure

end Stacks.Sites.ExtensionByZero.AnyUniverse

end
