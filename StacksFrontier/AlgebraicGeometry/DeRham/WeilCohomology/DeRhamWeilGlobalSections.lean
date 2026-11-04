module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.BottomDifferential
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.GlobalClassDegreeZero

/-!
# `H⁰_{dR}` of a smooth proper scheme over a field, and axiom (A8)

Let `X` be smooth and proper over a field `k`. The degree-zero de Rham differential vanishes on
global functions (Lemma 0FW5), and global sections are left exact, so

`H⁰_{dR}(X/k) = Γ(X, Ω⁰_{X/k}) = Γ(X, 𝒪_X)`,

every class being the class of a unique global function. This identification is natural: the
pullback `g^* : H⁰_{dR}(T/k) ⟶ H⁰_{dR}(X/k)` along a morphism `g : X ⟶ T` of smooth proper
`k`-schemes is the map `g^♯ : Γ(T, 𝒪_T) ⟶ Γ(X, 𝒪_X)`. In particular `g^*` is bijective on
`H⁰_{dR}` as soon as `g^♯` is bijective on global functions, which for `T = Spec Γ(X, 𝒪_X)` is
the axiom (A8) of Weil Cohomology Theories, Section 0FID, in the form used in Section 0FWC.

## Main results

* `Stacks.DeRhamWeil.bijective_smul_one_formsZero`: `Γ(X, 𝒪_X) ⟶ Γ(X, Ω⁰_{X/S})`, `r ↦ r · 1`,
  is bijective.
* `Stacks.DeRhamWeil.bijective_deRhamPushforwardInt_zero_top`: the canonical map of de Rham
  complexes of a commutative square is bijective in degree `0` on global sections when `g'^♯` is
  bijective on global functions.
* `Stacks.DeRhamWeil.bijective_pullbackPiece_zero`: **`g^*` is bijective on `H⁰_{dR}`** for a
  morphism `g` of smooth projective `k`-schemes bijective on global functions.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FW5](https://stacks.math.columbia.edu/tag/0FW5)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (sectionsComplex globalClass)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamWeil

section Forms

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **`Γ(X, Ω⁰_{X/S}) = Γ(X, 𝒪_X)`**: every degree-zero form on an open is a unique function
multiple of the unit. -/
theorem bijective_smul_one_formsZero (U : (X.Opens)ᵒᵖ) :
    Function.Bijective (fun r : X.sheaf.obj.obj U =>
      r • (Scheme.Hom.deRhamAlgebras p).exterior.one.eval U) := by
  refine ⟨fun r s hrs => ?_, fun x =>
    (Scheme.Hom.deRhamAlgebras p).exists_exterior_eq_smul_one U x⟩
  have h := congrArg ((Scheme.Hom.deRhamAlgebras p).exteriorPieceZeroIsoUnit.hom.val.app U) hrs
  rw [map_smul, map_smul] at h
  simp only [(Scheme.Hom.deRhamAlgebras p).exteriorPieceZeroIsoUnit_one U] at h
  have h' : r * 1 = s * 1 := h
  simpa using h'

end Forms

/-- If `f ∘ u = v ∘ w` with `u`, `v`, `w` bijective, then `f` is bijective. -/
private theorem bijective_of_comp_eq_comp {α β γ δ : Type*} {f : α → β} {u : γ → α} {v : δ → β}
    {w : γ → δ} (e : f ∘ u = v ∘ w) (hu : Function.Bijective u) (hv : Function.Bijective v)
    (hw : Function.Bijective w) : Function.Bijective f := by
  have h := hv.comp hw
  rw [← e] at h
  exact (Function.Bijective.of_comp_iff _ hu).1 h

section Square

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The canonical map of de Rham complexes in degree `0` on global sections sends `r · 1` to
`g'^♯(r) · 1`. -/
theorem deRhamFormsPushforwardHom_zero_top_smul_one (r : X.sheaf.obj.obj (op ⊤)) :
    ((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app 0).val.app (op ⊤)
        (r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op ⊤)) =
      (show X'.sheaf.obj.obj (op ⊤) from (g'.app ⊤).hom r) •
        (Scheme.Hom.deRhamAlgebras f').exterior.one.eval (op ⊤) := by
  refine (Scheme.Hom.deRhamFormsPushforwardHom_smul g' f f' g w 0 (op ⊤) r _).trans ?_
  have h1 : ((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app 0).val.app (op ⊤)
      ((Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op ⊤)) =
        (Scheme.Hom.deRhamAlgebras f').exterior.one.eval (op ⊤) :=
    (Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).map_one (op ⊤)
  rw [h1]
  rfl

/-- **The canonical map of de Rham complexes is bijective in degree `0` on global sections** when
`g'^♯ : Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is bijective. -/
theorem bijective_deRhamFormsPushforwardHom_zero_top (h : Function.Bijective (g'.app ⊤).hom) :
    Function.Bijective
      (((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app 0).val.app (op ⊤)) := by
  have e : (((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app 0).val.app (op ⊤)) ∘
      (fun r : X.sheaf.obj.obj (op ⊤) =>
        r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op ⊤)) =
      (fun r : X'.sheaf.obj.obj (op ⊤) =>
        r • (Scheme.Hom.deRhamAlgebras f').exterior.one.eval (op ⊤)) ∘ (g'.app ⊤).hom :=
    funext fun r => deRhamFormsPushforwardHom_zero_top_smul_one (g' := g') (f' := f') (f := f)
      (g := g) (w := w) r
  exact bijective_of_comp_eq_comp e (bijective_smul_one_formsZero f (op ⊤))
    (bijective_smul_one_formsZero f' (op ⊤)) h

/-- The components of an isomorphism of sheaves of modules are bijective on sections. -/
theorem bijective_iso_hom_val_app {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Bijective (e.hom.val.app U) :=
  ConcreteCategory.bijective_of_isIso ((_root_.SheafOfModules.evaluation R U).mapIso e).hom

/-- **The canonical map `Ω^•_{X/S} ⟶ g'_*Ω^•_{X'/S'}` of extended de Rham complexes is bijective
in degree `0` on global sections** when `g'^♯` is bijective on global functions. -/
theorem bijective_deRhamPushforwardInt_zero_top (h : Function.Bijective (g'.app ⊤).hom) :
    Function.Bijective (((deRhamPushforwardInt g' f' f g w).f ((0 : ℕ) : ℤ)).val.app (op ⊤)) := by
  have key : ⇑(((deRhamPushforwardInt g' f' f g w).f ((0 : ℕ) : ℤ)).val.app (op ⊤)) =
      ⇑(((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv.val.app
          (op ⊤)) ∘
        ⇑((formsPushforward g' f' f g w 0).val.app (op ⊤)) ∘
          ⇑(((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom.val.app
            (op ⊤)) := by
    rw [deRhamPushforwardInt_f g' f' f g w 0]
    rfl
  have hmid : ⇑((formsPushforward g' f' f g w 0).val.app (op ⊤)) =
      ⇑(((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app 0).val.app (op ⊤)) :=
    funext (formsPushforward_val_app g' f' f g w 0 (op ⊤))
  rw [key, hmid]
  exact (bijective_iso_hom_val_app
      ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).symm _).comp
    ((bijective_deRhamFormsPushforwardHom_zero_top g' f' f g w h).comp
      (bijective_iso_hom_val_app _ _))

end Square

/-! ### `H⁰_{dR}` over a field -/

section Field

variable {k : Type u} [Field k]

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p] [IsProper p]

/-- **The first differential of the complex of global sections of the de Rham complex vanishes**
for `X` smooth and proper over a field (Lemma 0FW5). -/
theorem sectionsComplex_deRhamComplexInt_d_zero_one :
    (sectionsComplex (inverseImageBase p) (deRhamComplexInt p)).d 0 1 = 0 := by
  change (Stacks.Cohomology.DerivedGlobalCupProduct.globalSections (inverseImageBase p)).map
    ((deRhamComplexInt p).d 0 1) = 0
  have hd : (deRhamComplexInt p).d 0 1 =
      ((deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫
        (deRhamComplexNat p).d 0 1 ≫
          ((deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv :=
    HomologicalComplex.extend_d_eq (deRhamComplexNat p) ComplexShape.embeddingUpNat rfl rfl
  rw [hd]
  ext x
  change ((deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv.val.app
      (op ⊤) (((deRhamComplexNat p).d 0 1).val.app (op ⊤)
        (((deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom.val.app
          (op ⊤) x)) = 0
  have h0 : ((deRhamComplexNat p).d 0 1).val.app (op ⊤) = 0 :=
    AlgebraicGeometry.deRhamComplex_d_zero_app_top_eq_zero k p (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential _)
  rw [h0]
  change ((deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv.val.app
      (op ⊤) 0 = 0
  exact map_zero _

/-- The inclusion of the cocycles in degree `0` of the global sections of the de Rham complex is
bijective. -/
theorem bijective_iCycles_zero :
    Function.Bijective ((sectionsComplex (inverseImageBase p) (deRhamComplexInt p)).iCycles 0) := by
  have := (sectionsComplex (inverseImageBase p) (deRhamComplexInt p)).isIso_iCycles 0 1 (by simp)
    (sectionsComplex_deRhamComplexInt_d_zero_one p)
  exact ConcreteCategory.bijective_of_isIso _

omit [Smooth p] [IsProper p] in
/-- **`H⁰_{dR}(X/k)` is the module of global degree-zero forms**: the class map
`Γ(X, Ω⁰_{X/k}) ⟶ H⁰_{dR}(X/k)` is bijective for `X` smooth and proper over `k`. -/
theorem bijective_globalClass_zero :
    Function.Bijective (globalClass (deRhamComplexInt p) 0) :=
  have : (deRhamComplexInt p).IsStrictlyGE 0 := isStrictlyGE_deRhamCochainComplex p
  Stacks.Cohomology.DerivedGlobalCupProduct.bijective_globalClass_zero _ _

variable {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) [Smooth q] [IsProper q] (g : X ⟶ T)
  (w : g ≫ q = p ≫ 𝟙 _)

/-- **Pullback is bijective on `H⁰_{dR}`** along a morphism `g : X ⟶ T` of smooth proper
`k`-schemes which is bijective on global functions: both `H⁰_{dR}` are the global functions, and
`g^*` is `g^♯`. -/
theorem bijective_deRhamPullbackSquare_zero (h : Function.Bijective (g.app ⊤).hom) :
    Function.Bijective (deRhamPullbackSquare g p q (𝟙 _) w 0) := by
  let eX := Equiv.ofBijective _ (bijective_iCycles_zero p)
  let eT := Equiv.ofBijective _ (bijective_iCycles_zero q)
  let φ := fun s => eX.symm (((deRhamPushforwardInt g p q (𝟙 _) w).f 0).val.app (op ⊤) (eT s))
  have hcomm : deRhamPullbackSquare g p q (𝟙 _) w 0 ∘ globalClass (deRhamComplexInt q) 0 =
      globalClass (deRhamComplexInt p) 0 ∘ φ := by
    funext s
    exact deRhamPullbackSquare_globalClass g p q (𝟙 _) w 0 s (φ s) (eX.apply_symm_apply _)
  exact bijective_of_comp_eq_comp hcomm (bijective_globalClass_zero q)
    (bijective_globalClass_zero p) (eX.symm.bijective.comp
      ((bijective_deRhamPushforwardInt_zero_top g p q (𝟙 _) w h).comp eT.bijective))

end Field

/-! ### Axiom (A8) -/

variable {k : Type u} [Field k] {X T : (SmoothProjectiveScheme k).FullSubcategory}

/-- **Axiom (A8) for de Rham cohomology, in the form of Section 0FWC**: for a morphism `g : X ⟶ T`
of smooth projective `k`-schemes which is bijective on global functions (for instance
`X ⟶ Spec Γ(X, 𝒪_X)`), the pullback `g^* : H⁰_{dR}(T/k) ⟶ H⁰_{dR}(X/k)` is bijective. -/
theorem bijective_pullbackPiece_zero (g : X ⟶ T)
    (h : Function.Bijective ((toScheme k).map g).appTop.hom) :
    Function.Bijective (pullbackPiece g 0) := by
  have := (isProjective X).isProper
  have := (isProjective T).isProper
  exact bijective_deRhamPullbackSquare_zero X.obj.hom T.obj.hom _ (square_w g) h

end Stacks.DeRhamWeil

end
