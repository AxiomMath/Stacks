module

public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeFiniteCover

/-!
# Glueing locally given derived objects over a finite open cover of a scheme

Let `X` be a scheme and `B` a property of opens of `X` stable under shrinking. Suppose given, for
every open `W` with `B W`, an object `K_W` of `D(𝒪_W)`, and for `W' ≤ W` isomorphisms
`ρ_{W'W} : K_W|_{W'} ≅ K_{W'}` satisfying the cocycle condition, such that the negative self-Ext
`Ext^{-1}(K_W, K_W)` vanishes for every such `W`. If finitely many opens with `B` cover `X`, there
is an object `K` of `D(𝒪_X)` with isomorphisms `K|_W ≅ K_W` for all `W` with `B W`, compatible
with the `ρ_{W'W}`.

The proof is by induction on the number of members of the cover. A solution over an open `Y` is
an object `K` of `D(𝒪_X)` with compatible isomorphisms `K|_W ≅ K_W` for `W ≤ Y`. Given one over
`Y` and a member `V`, the glueing lemma [Stacks, Tag 08DG] glues `K|_Y` and `K_V` along the
isomorphism on `Y ∩ V` given by the solution; on every `W ≤ Y ∪ V` the two resulting isomorphisms
on `W ∩ Y` and `W ∩ V` glue, uniquely because of the vanishing of negative self-Ext, to an
isomorphism on `W`.

## Main definitions

* `Stacks.Cohomology.GlueingComplexes.OpenSystem`: a system of locally given derived objects.
* `Stacks.Cohomology.GlueingComplexes.OpenSystem.SolutionOver`: a solution over an open.

## Main results

* `Stacks.Cohomology.GlueingComplexes.exists_restrict_eq_of_compatible`: glueing of morphisms
  into locally given objects along two opens.
* `Stacks.Cohomology.GlueingComplexes.OpenSystem.exists_solution`: a system of locally given
  objects with vanishing negative self-Ext comes from an object of `D(𝒪_X)`, for a finite cover.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedPullback (factorIso factorIso_assoc schemeFactorIso schemeFactorHom)
open scoped ZeroObject

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Two opens, for a ringed space -/

section TwoOpensRingedSpace

variable {X Y U V T : RingedSpace.{u, u}}

/-- The comparison on an intersection is the composite of the two comparisons through any
morphism to the ambient space. -/
theorem overlapIso_eq_factorIso (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : T ⟶ U) (iV : T ⟶ V)
    (h : iU ≫ jU = iV ≫ jV) (k : T ⟶ Y) (hkU : iU ≫ jU = k) (hkV : iV ≫ jV = k) :
    overlapIso jU jV iU iV h = factorIso iU jU k hkU ≪≫ (factorIso iV jV k hkV).symm := by
  subst hkU
  rw [overlapIso_eq_derivedRestrictSquareIso]
  rfl

private theorem glue_restrict_chase {C : Type*} [Category C]
    {P P' Q R AU AV LU0 LV0 LK sU sV ST : C}
    (KU : P ≅ Q) (KV : P' ≅ Q) (Kk : Q ≅ R) (PU : P ≅ AU) (PV : P' ≅ AV) (QU : AU ≅ R)
    (QV : AV ≅ R) (SU : LU0 ≅ sU) (SV : LV0 ≅ sV) (LU : LU0 ≅ LK) (LV : LV0 ≅ LK)
    (σTU : sU ≅ ST) (σTV : sV ≅ ST) (XU : AU ⟶ sU) (XV : AV ⟶ sV)
    (aU : KU.hom ≫ Kk.hom = PU.hom ≫ QU.hom) (aV : KV.hom ≫ Kk.hom = PV.hom ≫ QV.hom)
    (hσ : LU.inv ≫ SU.hom ≫ σTU.hom = LV.inv ≫ SV.hom ≫ σTV.hom)
    (hx : QU.inv ≫ XU ≫ σTU.hom = QV.inv ≫ XV ≫ σTV.hom) :
    PU.hom ≫ XU ≫ SU.inv ≫ LU.hom ≫ LV.inv = KU.hom ≫ KV.inv ≫ PV.hom ≫ XV ≫ SV.inv := by
  have e₁ : PU.hom = KU.hom ≫ Kk.hom ≫ QU.inv := by
    rw [← Category.assoc, aU]
    simp
  have e₂ : PV.hom = KV.hom ≫ Kk.hom ≫ QV.inv := by
    rw [← Category.assoc, aV]
    simp
  have e₃ : XU = QU.hom ≫ QV.inv ≫ XV ≫ σTV.hom ≫ σTU.inv := by
    simpa using congrArg (fun t => QU.hom ≫ t ≫ σTU.inv) hx
  have e₄ : SU.inv ≫ LU.hom = σTU.hom ≫ σTV.inv ≫ SV.inv ≫ LV.hom := by
    simpa using (congrArg (fun t => SU.inv ≫ LU.hom ≫ t ≫ σTV.inv ≫ SV.inv ≫ LV.hom) hσ).symm
  rw [e₁, e₂, e₃]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% e₄]
  simp

/-- **Glueing morphisms into locally given objects along two opens.** Let `U`, `V` be open in `Y`
with intersection `T` and covering `Y`, all mapping to `X` compatibly, let `F` be an object on `X`
and `S_Y`, `S_U`, `S_V`, `S_T` objects on `Y`, `U`, `V`, `T` with restriction isomorphisms
`σ` satisfying the cocycle condition on `T`. Two morphisms `F|_U ⟶ S_U`, `F|_V ⟶ S_V` with the
same restriction `F|_T ⟶ S_T` are the restrictions of a morphism `F|_Y ⟶ S_Y`. -/
theorem exists_restrict_eq_of_compatible (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : T ⟶ U) (iV : T ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hpb : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (ιY : Y ⟶ X) (ιU : U ⟶ X) (ιV : V ⟶ X) (ιT : T ⟶ X)
    (hU : jU ≫ ιY = ιU) (hV : jV ≫ ιY = ιV) (hTU : iU ≫ ιU = ιT) (hTV : iV ≫ ιV = ιT)
    (k : T ⟶ Y) (hkU : iU ≫ jU = k) (hkV : iV ≫ jV = k) (F : DerivedModules X)
    {SY : DerivedModules Y} {SU : DerivedModules U} {SV : DerivedModules V}
    {ST : DerivedModules T} (σU : (derivedRestrict jU).obj SY ≅ SU)
    (σV : (derivedRestrict jV).obj SY ≅ SV) (σTU : (derivedRestrict iU).obj SU ≅ ST)
    (σTV : (derivedRestrict iV).obj SV ≅ ST)
    (hσ : (factorIso iU jU k hkU).inv.app SY ≫ (derivedRestrict iU).map σU.hom ≫ σTU.hom =
      (factorIso iV jV k hkV).inv.app SY ≫ (derivedRestrict iV).map σV.hom ≫ σTV.hom)
    (xU : (derivedRestrict ιU).obj F ⟶ SU) (xV : (derivedRestrict ιV).obj F ⟶ SV)
    (hx : (factorIso iU ιU ιT hTU).inv.app F ≫ (derivedRestrict iU).map xU ≫ σTU.hom =
      (factorIso iV ιV ιT hTV).inv.app F ≫ (derivedRestrict iV).map xV ≫ σTV.hom) :
    ∃ φ : (derivedRestrict ιY).obj F ⟶ SY,
      (factorIso jU ιY ιU hU).inv.app F ≫ (derivedRestrict jU).map φ ≫ σU.hom = xU ∧
        (factorIso jV ιY ιV hV).inv.app F ≫ (derivedRestrict jV).map φ ≫ σV.hom = xV := by
  have hk : k ≫ ιY = ιT := by rw [← hkU, Category.assoc, hU, hTU]
  obtain ⟨φ, hφU, hφV⟩ := exists_map_eq_of_compatible jU jV iU iV hpb cover
    ((derivedRestrict ιY).obj F) SY
    ((factorIso jU ιY ιU hU).hom.app F ≫ xU ≫ σU.inv)
    ((factorIso jV ιY ιV hV).hom.app F ≫ xV ≫ σV.inv) (by
      have aU := congrArg Iso.hom (factorIso_assoc iU jU ιY ιU k ιT hU hkU hk hTU F)
      have aV := congrArg Iso.hom (factorIso_assoc iV jV ιY ιV k ιT hV hkV hk hTV F)
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at aU aV
      rw [overlapIso_eq_factorIso jU jV iU iV hpb.w k hkU hkV]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
        Category.assoc]
      exact glue_restrict_chase ((factorIso iU jU k hkU).app _)
        ((factorIso iV jV k hkV).app _) ((factorIso k ιY ιT hk).app F)
        ((derivedRestrict iU).mapIso ((factorIso jU ιY ιU hU).app F))
        ((derivedRestrict iV).mapIso ((factorIso jV ιY ιV hV).app F))
        ((factorIso iU ιU ιT hTU).app F) ((factorIso iV ιV ιT hTV).app F)
        ((derivedRestrict iU).mapIso σU) ((derivedRestrict iV).mapIso σV)
        ((factorIso iU jU k hkU).app SY) ((factorIso iV jV k hkV).app SY) σTU σTV
        ((derivedRestrict iU).map xU) ((derivedRestrict iV).map xV) aU aV hσ hx)
  refine ⟨φ, ?_, ?_⟩
  · rw [hφU]
    simp
  · rw [hφV]
    simp

/-- **Uniqueness of morphisms into locally given objects glued along two opens.** In the
situation of `exists_restrict_eq_of_compatible`, if every morphism `(F|_T)[1] ⟶ S_T` vanishes,
two morphisms `F|_Y ⟶ S_Y` with the same restrictions to `U` and to `V` are equal. -/
theorem eq_of_restrict_eq (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : T ⟶ U) (iV : T ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hpb : IsPullback iU iV jU jV)
    (cover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (ιY : Y ⟶ X) (ιU : U ⟶ X) (ιV : V ⟶ X) (ιT : T ⟶ X)
    (hU : jU ≫ ιY = ιU) (hV : jV ≫ ιY = ιV) (hTV : iV ≫ ιV = ιT) (F : DerivedModules X)
    {SY : DerivedModules Y} {SU : DerivedModules U} {SV : DerivedModules V}
    {ST : DerivedModules T} (σU : (derivedRestrict jU).obj SY ≅ SU)
    (σV : (derivedRestrict jV).obj SY ≅ SV) (σTV : (derivedRestrict iV).obj SV ≅ ST)
    (hExt : ∀ g : ((derivedRestrict ιT).obj F)⟦(1 : ℤ)⟧ ⟶ ST, g = 0)
    (φ ψ : (derivedRestrict ιY).obj F ⟶ SY)
    (h₁ : (factorIso jU ιY ιU hU).inv.app F ≫ (derivedRestrict jU).map φ ≫ σU.hom =
      (factorIso jU ιY ιU hU).inv.app F ≫ (derivedRestrict jU).map ψ ≫ σU.hom)
    (h₂ : (factorIso jV ιY ιV hV).inv.app F ≫ (derivedRestrict jV).map φ ≫ σV.hom =
      (factorIso jV ιY ιV hV).inv.app F ≫ (derivedRestrict jV).map ψ ≫ σV.hom) :
    φ = ψ := by
  have : (derivedRestrict jU).Additive := inferInstance
  have : (derivedRestrict jV).Additive := inferInstance
  have e₁ : (derivedRestrict jU).map φ = (derivedRestrict jU).map ψ :=
    (Iso.cancel_iso_hom_right _ _ σU).mp
      ((Iso.cancel_iso_inv_left ((factorIso jU ιY ιU hU).app F) _ _).mp h₁)
  have e₂ : (derivedRestrict jV).map φ = (derivedRestrict jV).map ψ :=
    (Iso.cancel_iso_hom_right _ _ σV).mp
      ((Iso.cancel_iso_inv_left ((factorIso jV ιY ιV hV).app F) _ _).mp h₂)
  have hc : (iV ≫ jV) ≫ ιY = ιT := by rw [Category.assoc, hV, hTV]
  let S : (derivedRestrict (iV ≫ jV)).obj (((derivedRestrict ιY).obj F)⟦(1 : ℤ)⟧) ≅
      ((derivedRestrict ιT).obj F)⟦(1 : ℤ)⟧ :=
    ((derivedRestrict (iV ≫ jV)).commShiftIso (1 : ℤ)).app ((derivedRestrict ιY).obj F) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso ((factorIso (iV ≫ jV) ιY ιT hc).app F)
  let R : (derivedRestrict iV).obj ((derivedRestrict jV).obj SY) ≅ ST :=
    (derivedRestrict iV).mapIso σV ≪≫ σTV
  rw [← sub_eq_zero]
  refine eq_zero_of_restrict_eq_zero jU jV iU iV hpb cover (φ - ψ)
    (by rw [Functor.map_sub, e₁, sub_self]) (by rw [Functor.map_sub, e₂, sub_self]) fun g => ?_
  calc g = S.hom ≫ (S.inv ≫ g ≫ R.hom) ≫ R.inv := by simp
    _ = 0 := by rw [hExt (S.inv ≫ g ≫ R.hom), zero_comp, comp_zero]

end TwoOpensRingedSpace

/-! ### Locally given objects on the opens of a scheme -/

section Scheme

variable {X : Scheme.{u}}

/-- **A system of locally given derived objects** on the opens of `X` with a property `B`: an
object `K_W` of `D(𝒪_W)` for every such open, and isomorphisms `K_W|_{W'} ≅ K_{W'}` for `W' ≤ W`
satisfying the cocycle condition (Situation [Stacks, Tag 0D67], restriction being derived
pullback). -/
structure OpenSystem (B : X.Opens → Prop) where
  /-- The object `K_W` on `W`. -/
  obj (W : X.Opens) (hW : B W) : DerivedModules W.toScheme.toRingedSpace
  /-- The restriction isomorphism `K_W|_{W'} ≅ K_{W'}`. -/
  iso {W' W : X.Opens} (h : W' ≤ W) (hW : B W) (hW' : B W') :
    (derivedRestrict (X.homOfLE h).toLRSHom.toShHom).obj (obj W hW) ≅ obj W' hW'
  /-- The cocycle condition. -/
  cocycle {W'' W' W : X.Opens} (h₁ : W'' ≤ W') (h₂ : W' ≤ W) (hW : B W) (hW' : B W')
    (hW'' : B W'') :
    (iso (h₁.trans h₂) hW hW'').hom =
      (factorIso (X.homOfLE h₁).toLRSHom.toShHom (X.homOfLE h₂).toLRSHom.toShHom
          (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom
          (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
            (X.homOfLE_homOfLE h₁ h₂))).inv.app (obj W hW) ≫
        (derivedRestrict (X.homOfLE h₁).toLRSHom.toShHom).map (iso h₂ hW hW').hom ≫
          (iso h₁ hW' hW'').hom

namespace OpenSystem

variable {B : X.Opens → Prop} (S : OpenSystem B)

/-- The restriction to `W' ≤ W` of a morphism `F|_W ⟶ K_W`. -/
def res (F : DerivedModules X.toRingedSpace) {W' W : X.Opens} (h : W' ≤ W) (hW : B W)
    (hW' : B W') (x : (derivedRestrict W.ι.toLRSHom.toShHom).obj F ⟶ S.obj W hW) :
    (derivedRestrict W'.ι.toLRSHom.toShHom).obj F ⟶ S.obj W' hW' :=
  (factorIso (X.homOfLE h).toLRSHom.toShHom W.ι.toLRSHom.toShHom W'.ι.toLRSHom.toShHom
      (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h))).inv.app F ≫
    (derivedRestrict (X.homOfLE h).toLRSHom.toShHom).map x ≫ (S.iso h hW hW').hom

private theorem res_res_chase {C : Type*} [Category C] {A A₃ A₁ A₀ D D₃ D₁ D₀ : C}
    (φF : A ≅ A₃) (f₃ : A₃ ≅ A₀) (f₂ : A ≅ A₁) (f₁ : A₁ ≅ A₀) (φS : D ≅ D₃) (i₂ : D ≅ D₁)
    (i₁ : D₁ ≅ D₀) (x'' : A ⟶ D) (x₃ : A₃ ⟶ D₃) (i₃ : D₃ ⟶ D₀)
    (hassoc : φF.hom ≫ f₃.hom = f₂.hom ≫ f₁.hom) (nat : x'' ≫ φS.hom = φF.hom ≫ x₃)
    (hcoc : i₃ = φS.inv ≫ i₂.hom ≫ i₁.hom) :
    f₁.inv ≫ (f₂.inv ≫ x'' ≫ i₂.hom) ≫ i₁.hom = f₃.inv ≫ x₃ ≫ i₃ := by
  have e₁ : f₁.inv ≫ f₂.inv = f₃.inv ≫ φF.inv := by
    simpa using congrArg (fun t => f₁.inv ≫ f₂.inv ≫ t ≫ f₃.inv ≫ φF.inv) hassoc
  have e₂ : x₃ ≫ φS.inv = φF.inv ≫ x'' := by
    simpa using (congrArg (fun t => φF.inv ≫ t ≫ φS.inv) nat).symm
  rw [hcoc]
  simp only [Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂]

/-- Restriction of morphisms into the system is transitive. -/
theorem res_res (F : DerivedModules X.toRingedSpace) {W'' W' W : X.Opens} (h₁ : W'' ≤ W')
    (h₂ : W' ≤ W) (hW : B W) (hW' : B W') (hW'' : B W'')
    (x : (derivedRestrict W.ι.toLRSHom.toShHom).obj F ⟶ S.obj W hW) :
    S.res F h₁ hW' hW'' (S.res F h₂ hW hW' x) = S.res F (h₁.trans h₂) hW hW'' x := by
  have hassoc := congrArg Iso.hom (factorIso_assoc (X.homOfLE h₁).toLRSHom.toShHom
    (X.homOfLE h₂).toLRSHom.toShHom W.ι.toLRSHom.toShHom W'.ι.toLRSHom.toShHom
    (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom W''.ι.toLRSHom.toShHom
    (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₂))
    (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
      (X.homOfLE_homOfLE h₁ h₂))
    (congrArg (fun m : W''.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι (h₁.trans h₂)))
    (congrArg (fun m : W''.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₁)) F)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hassoc
  have nat := (factorIso (X.homOfLE h₁).toLRSHom.toShHom (X.homOfLE h₂).toLRSHom.toShHom
    (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom
    (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
      (X.homOfLE_homOfLE h₁ h₂))).hom.naturality x
  simp only [Functor.comp_map] at nat
  simp only [res, Functor.map_comp]
  exact res_res_chase
    ((factorIso (X.homOfLE h₁).toLRSHom.toShHom (X.homOfLE h₂).toLRSHom.toShHom
      (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom
      (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
        (X.homOfLE_homOfLE h₁ h₂))).app _)
    ((factorIso (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom W.ι.toLRSHom.toShHom
      W''.ι.toLRSHom.toShHom
      (congrArg (fun m : W''.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
        (X.homOfLE_ι (h₁.trans h₂)))).app F)
    ((derivedRestrict (X.homOfLE h₁).toLRSHom.toShHom).mapIso
      ((factorIso (X.homOfLE h₂).toLRSHom.toShHom W.ι.toLRSHom.toShHom W'.ι.toLRSHom.toShHom
        (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₂))).app F))
    ((factorIso (X.homOfLE h₁).toLRSHom.toShHom W'.ι.toLRSHom.toShHom W''.ι.toLRSHom.toShHom
      (congrArg (fun m : W''.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₁))).app F)
    ((factorIso (X.homOfLE h₁).toLRSHom.toShHom (X.homOfLE h₂).toLRSHom.toShHom
      (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom
      (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
        (X.homOfLE_homOfLE h₁ h₂))).app _)
    ((derivedRestrict (X.homOfLE h₁).toLRSHom.toShHom).mapIso (S.iso h₂ hW hW'))
    (S.iso h₁ hW' hW'') _ _ _ hassoc nat (S.cocycle h₁ h₂ hW hW' hW'')

/-- Restricting a morphism precomposed with a morphism of restrictions of global objects. -/
theorem res_comp (F F' : DerivedModules X.toRingedSpace) {W' W : X.Opens} (h : W' ≤ W)
    (hW : B W) (hW' : B W')
    (z : (derivedRestrict W.ι.toLRSHom.toShHom).obj F' ⟶
      (derivedRestrict W.ι.toLRSHom.toShHom).obj F)
    (x : (derivedRestrict W.ι.toLRSHom.toShHom).obj F ⟶ S.obj W hW) :
    S.res F' h hW hW' (z ≫ x) = restrictHom F' F h z ≫ S.res F h hW hW' x := by
  simp only [res, restrictHom, schemeFactorHom, schemeFactorIso, Iso.homCongr_apply,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **A solution over an open `Y`** of a system of locally given objects: an object `F` of
`D(𝒪_X)` with isomorphisms `F|_W ≅ K_W` for every `W ≤ Y` with `B W`, compatible with the
restriction isomorphisms of the system. -/
structure SolutionOver (Y : X.Opens) where
  /-- The object of `D(𝒪_X)`. -/
  F : DerivedModules X.toRingedSpace
  /-- The identification of its restriction to `W` with `K_W`. -/
  iso (W : X.Opens) (hWY : W ≤ Y) (hW : B W) :
    (derivedRestrict W.ι.toLRSHom.toShHom).obj F ≅ S.obj W hW
  /-- The identifications are compatible with restriction. -/
  compat {W' W : X.Opens} (h : W' ≤ W) (hWY : W ≤ Y) (hW : B W) (hW' : B W') :
    (iso W' (h.trans hWY) hW').hom = S.res F h hW hW' (iso W hWY hW).hom

variable {S}

/-- A solution over `Y` is one over every smaller open. -/
def SolutionOver.mono {Y Y' : X.Opens} (sol : S.SolutionOver Y) (h : Y' ≤ Y) :
    S.SolutionOver Y' where
  F := sol.F
  iso W hW hBW := sol.iso W (hW.trans h) hBW
  compat h' hWY hW hW' := sol.compat h' (hWY.trans h) hW hW'

/-- An open contained in the empty open is an empty scheme. -/
theorem isEmpty_toScheme_of_le_bot {W : X.Opens} (h : W ≤ ⊥) : IsEmpty W.toScheme :=
  ⟨fun x => by simpa using h x.2⟩

variable (S) in
/-- The solution over the empty open. -/
def SolutionOver.bot : S.SolutionOver ⊥ where
  F := 0
  iso _W hW _ :=
    haveI := isEmpty_toScheme_of_le_bot hW
    { hom := 0
      inv := 0
      hom_inv_id := (subsingleton_hom_derivedCategory_of_isEmpty _ _).elim _ _
      inv_hom_id := (subsingleton_hom_derivedCategory_of_isEmpty _ _).elim _ _ }
  compat h hWY _ _ :=
    haveI := isEmpty_toScheme_of_le_bot (h.trans hWY)
    (subsingleton_hom_derivedCategory_of_isEmpty _ _).elim _ _


variable (S) in
/-- **Glueing morphisms into the system along two opens.** If `W ⊆ W₁ ∪ W₂`, two morphisms
`F|_{W₁} ⟶ K_{W₁}` and `F|_{W₂} ⟶ K_{W₂}` with the same restriction to `W₁ ∩ W₂` are the
restrictions of a morphism `F|_W ⟶ K_W`. -/
theorem exists_res_eq_of_le_sup (F : DerivedModules X.toRingedSpace) {W₁ W₂ W : X.Opens}
    (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (hcov : W ≤ W₁ ⊔ W₂) (hW : B W) (hW₁ : B W₁) (hW₂ : B W₂)
    (hW₁₂ : B (W₁ ⊓ W₂))
    (x₁ : (derivedRestrict W₁.ι.toLRSHom.toShHom).obj F ⟶ S.obj W₁ hW₁)
    (x₂ : (derivedRestrict W₂.ι.toLRSHom.toShHom).obj F ⟶ S.obj W₂ hW₂)
    (hx : S.res F (inf_le_left : W₁ ⊓ W₂ ≤ W₁) hW₁ hW₁₂ x₁ =
      S.res F (inf_le_right : W₁ ⊓ W₂ ≤ W₂) hW₂ hW₁₂ x₂) :
    ∃ φ, S.res F h₁ hW hW₁ φ = x₁ ∧ S.res F h₂ hW hW₂ φ = x₂ :=
  exists_restrict_eq_of_compatible (X.homOfLE h₁).toLRSHom.toShHom
    (X.homOfLE h₂).toLRSHom.toShHom (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).toLRSHom.toShHom
    (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).toLRSHom.toShHom
    (Scheme.isPullback_toShHom (isPullback_opens_inf_le h₁ h₂))
    (range_homOfLE_union h₁ h₂ hcov) W.ι.toLRSHom.toShHom W₁.ι.toLRSHom.toShHom
    W₂.ι.toLRSHom.toShHom (W₁ ⊓ W₂).ι.toLRSHom.toShHom
    (congrArg (fun m : W₁.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₁))
    (congrArg (fun m : W₂.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₂))
    (congrArg (fun m : (W₁ ⊓ W₂).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_left : W₁ ⊓ W₂ ≤ W₁)))
    (congrArg (fun m : (W₁ ⊓ W₂).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_right : W₁ ⊓ W₂ ≤ W₂)))
    (X.homOfLE ((inf_le_left : W₁ ⊓ W₂ ≤ W₁).trans h₁)).toLRSHom.toShHom
    (congrArg (fun m : (W₁ ⊓ W₂).toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
      (X.homOfLE_homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁) h₁))
    (congrArg (fun m : (W₁ ⊓ W₂).toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
      (X.homOfLE_homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂) h₂)) F
    (S.iso h₁ hW hW₁) (S.iso h₂ hW hW₂) (S.iso inf_le_left hW₁ hW₁₂)
    (S.iso inf_le_right hW₂ hW₁₂)
    ((S.cocycle inf_le_left h₁ hW hW₁ hW₁₂).symm.trans
      (S.cocycle inf_le_right h₂ hW hW₂ hW₁₂)) x₁ x₂ hx

variable (S) in
/-- **Uniqueness of morphisms into the system glued along two opens.** If `W ⊆ W₁ ∪ W₂` and every
morphism `(F|_{W₁ ∩ W₂})[1] ⟶ K_{W₁ ∩ W₂}` vanishes, two morphisms `F|_W ⟶ K_W` with the same
restrictions to `W₁` and to `W₂` are equal. -/
theorem eq_of_res_eq (F : DerivedModules X.toRingedSpace) {W₁ W₂ W : X.Opens}
    (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (hcov : W ≤ W₁ ⊔ W₂) (hW : B W) (hW₁ : B W₁) (hW₂ : B W₂)
    (hW₁₂ : B (W₁ ⊓ W₂))
    (hExt : ∀ g : ((derivedRestrict (W₁ ⊓ W₂).ι.toLRSHom.toShHom).obj F)⟦(1 : ℤ)⟧ ⟶
      S.obj (W₁ ⊓ W₂) hW₁₂, g = 0)
    (φ ψ : (derivedRestrict W.ι.toLRSHom.toShHom).obj F ⟶ S.obj W hW)
    (e₁ : S.res F h₁ hW hW₁ φ = S.res F h₁ hW hW₁ ψ)
    (e₂ : S.res F h₂ hW hW₂ φ = S.res F h₂ hW hW₂ ψ) : φ = ψ :=
  eq_of_restrict_eq (X.homOfLE h₁).toLRSHom.toShHom
    (X.homOfLE h₂).toLRSHom.toShHom (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).toLRSHom.toShHom
    (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).toLRSHom.toShHom
    (Scheme.isPullback_toShHom (isPullback_opens_inf_le h₁ h₂))
    (range_homOfLE_union h₁ h₂ hcov) W.ι.toLRSHom.toShHom W₁.ι.toLRSHom.toShHom
    W₂.ι.toLRSHom.toShHom (W₁ ⊓ W₂).ι.toLRSHom.toShHom
    (congrArg (fun m : W₁.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₁))
    (congrArg (fun m : W₂.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h₂))
    (congrArg (fun m : (W₁ ⊓ W₂).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_right : W₁ ⊓ W₂ ≤ W₂))) F
    (S.iso h₁ hW hW₁) (S.iso h₂ hW hW₂) (S.iso inf_le_right hW₂ hW₁₂) hExt φ ψ e₁ e₂

/-- A morphism restricting to isomorphisms on two opens covering `W` is an isomorphism. -/
theorem isIso_of_res_isIso (F : DerivedModules X.toRingedSpace) {W₁ W₂ W : X.Opens}
    (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (hcov : W ≤ W₁ ⊔ W₂) (hW : B W) (hW₁ : B W₁) (hW₂ : B W₂)
    (φ : (derivedRestrict W.ι.toLRSHom.toShHom).obj F ⟶ S.obj W hW)
    (i₁ : IsIso (S.res F h₁ hW hW₁ φ)) (i₂ : IsIso (S.res F h₂ hW hW₂ φ)) : IsIso φ := by
  have key : ∀ {W₁ : X.Opens} (h : W₁ ≤ W) (hW₁ : B W₁), IsIso (S.res F h hW hW₁ φ) →
      IsIso ((derivedRestrict (X.homOfLE h).toLRSHom.toShHom).map φ) := fun {W₁} h hW₁ i => by
    have e : (derivedRestrict (X.homOfLE h).toLRSHom.toShHom).map φ =
        (factorIso (X.homOfLE h).toLRSHom.toShHom W.ι.toLRSHom.toShHom W₁.ι.toLRSHom.toShHom
          (congrArg (fun m : W₁.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h))).hom.app F ≫
          S.res F h hW hW₁ φ ≫ (S.iso h hW hW₁).inv := by
      simp [res]
    rw [e]
    infer_instance
  exact isIso_of_restrict_isIso (X.homOfLE h₁).toLRSHom.toShHom
    (X.homOfLE h₂).toLRSHom.toShHom (range_homOfLE_union h₁ h₂ hcov) φ (key h₁ hW₁ i₁)
    (key h₂ hW₂ i₂)

/-- Vanishing of negative self-Ext of `K_W` gives the vanishing of `Ext^{-1}(F|_W, K_W)` as soon
as `F|_W ≅ K_W`. -/
theorem shift_eq_zero_of_iso {W : X.Opens} {hW : B W} {A : DerivedModules W.toScheme.toRingedSpace}
    (e : A ≅ S.obj W hW) (hExt : ∀ g : (S.obj W hW)⟦(1 : ℤ)⟧ ⟶ S.obj W hW, g = 0)
    (g : A⟦(1 : ℤ)⟧ ⟶ S.obj W hW) : g = 0 := by
  calc g = (shiftFunctor _ (1 : ℤ)).map e.hom ≫ ((shiftFunctor _ (1 : ℤ)).map e.inv ≫ g) := by
        rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.id_comp]
    _ = 0 := by rw [hExt ((shiftFunctor _ (1 : ℤ)).map e.inv ≫ g), comp_zero]

/-! ### The induction step -/

section Step

variable {Y V : X.Opens} (sol : S.SolutionOver Y) (hV : B V) (hYV : B (Y ⊓ V))

/-- The identification on `Y ∩ V` along which a solution over `Y` and `K_V` are glued. -/
def glueIso :
    (derivedRestrict (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom).obj
        ((derivedRestrict Y.ι.toLRSHom.toShHom).obj sol.F) ≅
      (derivedRestrict (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom).obj
        (S.obj V hV) :=
  (schemeFactorIso (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)) Y.ι (Y ⊓ V).ι
      (X.homOfLE_ι _)).app sol.F ≪≫ sol.iso (Y ⊓ V) inf_le_left hYV ≪≫
    (S.iso inf_le_right hV hYV).symm

variable (G : Glueing Y.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom
  (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom
  (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom
  (Scheme.isPullback_toShHom (isPullback_opens_inf Y V)).w
  ((derivedRestrict Y.ι.toLRSHom.toShHom).obj sol.F) (S.obj V hV) (glueIso sol hV hYV))

/-- The glued object, identified with `K_W` on the opens `W ≤ Y` through the solution over `Y`. -/
def leftIso {W : X.Opens} (h : W ≤ Y) (hW : B W) :
    (derivedRestrict W.ι.toLRSHom.toShHom).obj G.F ≅ S.obj W hW :=
  ((schemeFactorIso (X.homOfLE h) Y.ι W.ι (X.homOfLE_ι h)).app G.F).symm ≪≫
    (derivedRestrict (X.homOfLE h).toLRSHom.toShHom).mapIso G.f ≪≫
    (schemeFactorIso (X.homOfLE h) Y.ι W.ι (X.homOfLE_ι h)).app sol.F ≪≫ sol.iso W h hW

/-- The glued object, identified with `K_W` on the opens `W ≤ V` through `K_V`. -/
def rightIso {W : X.Opens} (h : W ≤ V) (hW : B W) :
    (derivedRestrict W.ι.toLRSHom.toShHom).obj G.F ≅ S.obj W hW :=
  ((factorIso (X.homOfLE h).toLRSHom.toShHom V.ι.toLRSHom.toShHom W.ι.toLRSHom.toShHom
      (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h))).app G.F).symm ≪≫
    (derivedRestrict (X.homOfLE h).toLRSHom.toShHom).mapIso G.g ≪≫ S.iso h hV hW

/-- The forward map of `leftIso` is the restriction of `G.f` followed by the solution's
identification over `W`. -/
theorem leftIso_hom {W : X.Opens} (h : W ≤ Y) (hW : B W) :
    (leftIso sol hV hYV G h hW).hom =
      restrictHom G.F sol.F h G.f.hom ≫ (sol.iso W h hW).hom := by
  simp [leftIso, restrictHom, schemeFactorHom]

/-- The forward map of `rightIso` is the restriction of `G.g` along `W ≤ V`. -/
theorem rightIso_hom {W : X.Opens} (h : W ≤ V) (hW : B W) :
    (rightIso sol hV hYV G h hW).hom = S.res G.F h hV hW G.g.hom := by
  simp [rightIso, res]

/-- Restricting `leftIso` over `W` to `W' ≤ W` gives `leftIso` over `W'`. -/
theorem res_leftIso {W' W : X.Opens} (h : W' ≤ W) (hWY : W ≤ Y) (hW : B W) (hW' : B W') :
    S.res G.F h hW hW' (leftIso sol hV hYV G hWY hW).hom =
      (leftIso sol hV hYV G (h.trans hWY) hW').hom := by
  rw [leftIso_hom, leftIso_hom, res_comp, restrictHom_restrictHom, sol.compat h hWY hW hW']

/-- Restricting `rightIso` over `W` to `W' ≤ W` gives `rightIso` over `W'`. -/
theorem res_rightIso {W' W : X.Opens} (h : W' ≤ W) (hWV : W ≤ V) (hW : B W) (hW' : B W') :
    S.res G.F h hW hW' (rightIso sol hV hYV G hWV hW).hom =
      (rightIso sol hV hYV G (h.trans hWV) hW').hom := by
  rw [rightIso_hom, rightIso_hom, res_res]

private theorem left_right_chase {C : Type*} [Category C] {a b c d e g k : C}
    (FY : a ≅ b) (FV : c ≅ b) (f : a ⟶ d) (fF : d ⟶ e) (s : e ⟶ g) (σ : k ≅ g) (r : c ⟶ k)
    (hc : f ≫ fF ≫ s ≫ σ.inv = FY.hom ≫ FV.inv ≫ r) :
    FY.inv ≫ f ≫ fF ≫ s = FV.inv ≫ r ≫ σ.hom := by
  simpa using congrArg (fun t => FY.inv ≫ t ≫ σ.hom) hc

/-- On `Y ∩ V`, the two identifications of the glued object agree: this is the compatibility of
the glueing. -/
theorem leftIso_inf_eq :
    (leftIso sol hV hYV G (inf_le_left : Y ⊓ V ≤ Y) hYV).hom =
      (rightIso sol hV hYV G (inf_le_right : Y ⊓ V ≤ V) hYV).hom := by
  have hc : (derivedRestrict (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom).map
      G.f.hom ≫ (glueIso sol hV hYV).hom =
      (overlapIso Y.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom
        (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom
        (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom
        (Scheme.isPullback_toShHom (isPullback_opens_inf Y V)).w).hom.app G.F ≫
      (derivedRestrict (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom).map G.g.hom :=
    G.compatible
  have hov := congrArg (fun i => i.hom.app G.F) (overlapIso_eq_factorIso Y.ι.toLRSHom.toShHom
    V.ι.toLRSHom.toShHom (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom
    (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom
    (Scheme.isPullback_toShHom (isPullback_opens_inf Y V)).w (Y ⊓ V).ι.toLRSHom.toShHom
    (congrArg (fun m : (Y ⊓ V).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_left : Y ⊓ V ≤ Y)))
    (congrArg (fun m : (Y ⊓ V).toScheme ⟶ X ↦ m.toLRSHom.toShHom)
      (X.homOfLE_ι (inf_le_right : Y ⊓ V ≤ V))))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hov
  rw [hov] at hc
  simp only [glueIso, schemeFactorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc] at hc
  simp only [leftIso, rightIso, schemeFactorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom]
  exact left_right_chase ((factorIso _ _ _ _).app G.F) ((factorIso _ _ _ _).app G.F) _ _ _ _ _ hc

/-- On every open of `Y ∩ V`, the two identifications of the glued object agree. -/
theorem leftIso_eq_rightIso {W : X.Opens} (hWY : W ≤ Y) (hWV : W ≤ V) (hW : B W) :
    (leftIso sol hV hYV G hWY hW).hom = (rightIso sol hV hYV G hWV hW).hom := by
  rw [← res_leftIso sol hV hYV G (le_inf hWY hWV) inf_le_left hYV hW,
    ← res_rightIso sol hV hYV G (le_inf hWY hWV) inf_le_right hYV hW, leftIso_inf_eq]

end Step


/-- **The induction step.** If `B` is stable under shrinking and negative self-Ext of the system
vanishes, a solution over `Y` and an open `V` with `B V` give a solution over `Y ∪ V`. -/
theorem SolutionOver.nonempty_sup (hB : ∀ {W' W : X.Opens}, W' ≤ W → B W → B W')
    (hExt : ∀ W hW (g : (S.obj W hW)⟦(1 : ℤ)⟧ ⟶ S.obj W hW), g = 0)
    {Y V : X.Opens} (sol : S.SolutionOver Y) (hV : B V) :
    Nonempty (S.SolutionOver (Y ⊔ V)) := by
  have hYV : B (Y ⊓ V) := hB inf_le_right hV
  obtain ⟨G⟩ := exists_glueing Y.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom
    (X.homOfLE (inf_le_left : Y ⊓ V ≤ Y)).toLRSHom.toShHom
    (X.homOfLE (inf_le_right : Y ⊓ V ≤ V)).toLRSHom.toShHom
    (Scheme.isPullback_toShHom (isPullback_opens_inf Y V))
    ((derivedRestrict Y.ι.toLRSHom.toShHom).obj sol.F) (S.obj V hV) (glueIso sol hV hYV)
  have key : ∀ (W : X.Opens) (hWY : W ≤ Y ⊔ V) (hW : B W),
      ∃ φ : (derivedRestrict W.ι.toLRSHom.toShHom).obj G.F ⟶ S.obj W hW, IsIso φ ∧
        S.res G.F (inf_le_left : W ⊓ Y ≤ W) hW (hB inf_le_left hW) φ =
          (leftIso sol hV hYV G inf_le_right (hB inf_le_left hW)).hom ∧
        S.res G.F (inf_le_left : W ⊓ V ≤ W) hW (hB inf_le_left hW) φ =
          (rightIso sol hV hYV G inf_le_right (hB inf_le_left hW)).hom := by
    intro W hWY hW
    have hcov : W ≤ W ⊓ Y ⊔ W ⊓ V := (le_inf le_rfl hWY).trans (inf_sup_left _ _ _).le
    obtain ⟨φ, e₁, e₂⟩ := S.exists_res_eq_of_le_sup G.F inf_le_left inf_le_left hcov hW
      (hB inf_le_left hW) (hB inf_le_left hW) (hB (inf_le_left.trans inf_le_left) hW) _ _
      ((res_leftIso sol hV hYV G inf_le_left inf_le_right _ _).trans
        ((leftIso_eq_rightIso sol hV hYV G (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right) _).trans
        (res_rightIso sol hV hYV G inf_le_right inf_le_right _ _).symm))
    refine ⟨φ, S.isIso_of_res_isIso G.F inf_le_left inf_le_left hcov hW (hB inf_le_left hW)
      (hB inf_le_left hW) φ ?_ ?_, e₁, e₂⟩
    · rw [e₁]; infer_instance
    · rw [e₂]; infer_instance
  choose φ hφ h₁ h₂ using key
  refine ⟨{ F := G.F
            iso := fun W hWY hW => have := hφ W hWY hW; asIso (φ W hWY hW)
            compat := fun {W' W} h hWY hW hW' => ?_ }⟩
  change φ W' (h.trans hWY) hW' = S.res G.F h hW hW' (φ W hWY hW)
  have hcov' : W' ≤ W' ⊓ Y ⊔ W' ⊓ V := (le_inf le_rfl (h.trans hWY)).trans (inf_sup_left _ _ _).le
  have step : ∀ (T : X.Opens)
      (I : ∀ {W : X.Opens}, W ≤ T → ∀ hW : B W,
        (derivedRestrict W.ι.toLRSHom.toShHom).obj G.F ≅ S.obj W hW)
      (hI : ∀ {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (hWT : W₂ ≤ T) (hW₂ : B W₂) (hW₁ : B W₁),
        S.res G.F h hW₂ hW₁ (I hWT hW₂).hom = (I (h.trans hWT) hW₁).hom)
      (hφ : ∀ (W : X.Opens) (hWY : W ≤ Y ⊔ V) (hW : B W),
        S.res G.F (inf_le_left : W ⊓ T ≤ W) hW (hB inf_le_left hW) (φ W hWY hW) =
          (I inf_le_right (hB inf_le_left hW)).hom),
      S.res G.F (inf_le_left : W' ⊓ T ≤ W') hW' (hB inf_le_left hW') (φ W' (h.trans hWY) hW') =
        S.res G.F (inf_le_left : W' ⊓ T ≤ W') hW' (hB inf_le_left hW')
          (S.res G.F h hW hW' (φ W hWY hW)) := fun T I hI hφ => by
    rw [hφ W' _ hW', ← hI (inf_le_inf_right T h) inf_le_right (hB inf_le_left hW)
      (hB inf_le_left hW'), ← hφ W hWY hW, S.res_res, S.res_res]
  exact S.eq_of_res_eq G.F (inf_le_left : W' ⊓ Y ≤ W') (inf_le_left : W' ⊓ V ≤ W') hcov' hW'
    (hB inf_le_left hW') (hB inf_le_left hW') (hB (inf_le_left.trans inf_le_left) hW')
    (S.shift_eq_zero_of_iso
      (leftIso sol hV hYV G (inf_le_left.trans inf_le_right)
        (hB (inf_le_left.trans inf_le_left) hW'))
      (hExt _ _)) _ _
    (step Y (fun hW' hW => leftIso sol hV hYV G hW' hW)
      (fun h' hWT hW₂ hW₁ => res_leftIso sol hV hYV G h' hWT hW₂ hW₁) h₁)
    (step V (fun hW' hW => rightIso sol hV hYV G hW' hW)
      (fun h' hWT hW₂ hW₁ => res_rightIso sol hV hYV G h' hWT hW₂ hW₁) h₂)

variable (S) in
/-- **Locally given derived objects glue over a finite cover.** Let `B` be a property of opens of
`X` stable under shrinking, and `(K_W, ρ_{W'W})` a system of locally given objects on the opens
with `B` whose negative self-Ext `Ext^{-1}(K_W, K_W)` vanishes. If finitely many opens with `B`
cover `X`, there is a solution over `X`: an object `F` of `D(𝒪_X)` with isomorphisms
`F|_W ≅ K_W` for all `W` with `B W`, compatible with the `ρ_{W'W}`. -/
theorem exists_solution (hB : ∀ {W' W : X.Opens}, W' ≤ W → B W → B W')
    (hExt : ∀ W hW (g : (S.obj W hW)⟦(1 : ℤ)⟧ ⟶ S.obj W hW), g = 0)
    {ι : Type*} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, B (U i)) (hcov : ⨆ i, U i = ⊤) :
    Nonempty (S.SolutionOver ⊤) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, Nonempty (S.SolutionOver (s.sup U)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨(SolutionOver.bot S).mono Finset.sup_empty.le⟩
    | @insert j s _ ih =>
      obtain ⟨sol⟩ := ih
      obtain ⟨sol'⟩ := sol.nonempty_sup hB hExt (hU j)
      exact ⟨sol'.mono (by rw [Finset.sup_insert, sup_comm])⟩
  obtain ⟨sol⟩ := key Finset.univ
  exact ⟨sol.mono (by rw [Finset.sup_univ_eq_iSup, hcov])⟩

end OpenSystem

end Scheme

end Stacks.Cohomology.GlueingComplexes

end
