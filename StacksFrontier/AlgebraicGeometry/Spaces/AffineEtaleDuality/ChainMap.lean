module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Linearity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.KInjectiveSections
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# The chain-level comparison map of Stacks 0E50

Let `P` and `I` be complexes of `A`-modules, `J` a complex of `𝒪_étale`-modules on the small
étale site of `Spec A`, and `ι : ε^* Ĩ ⟶ J` a morphism of complexes. This file constructs the
morphism of complexes of `𝒪_étale`-modules

`ψ : (ε^* Hom^•_A(P, I)~)^{lift} ⟶ SheafHom^•(ε^* P̃, J)`,

the universe lift being the sectionwise lift into the module universe of the internal Hom complex.
In degree `n` it is the morphism out of the quasi-coherent module `ε^* (Hom^n_A(P, I))~`
determined, through `ε^*T ⊣ Γ`, by the `A`-linear map sending a cochain `d : P ⟶ I[n]` to the
global section of the internal Hom complex whose local cochain over `⊤` is `ι ∘ ε^*T(d)`.

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.globalCochain`: the cochain `ι ∘ ε^*T(d)`.
* `AlgebraicGeometry.AffineEtaleDuality.topSection`: the corresponding section over `⊤` of the
  internal Hom complex.
* `AlgebraicGeometry.AffineEtaleDuality.compMap`: the morphism of complexes `ψ`.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.phiN_app_top`: the degree-`n` component of `ψ` sends the
  canonical global section attached to `d` to the section attached to `ι ∘ ε^*T(d)`. That component
  is `ψ` itself in that degree, by `AlgebraicGeometry.AffineEtaleDuality.compMap_f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The small étale ringed site of `Spec A`. -/
abbrev Xs : RingedSite.{u + 1, u, u} := smallEtaleRingedSite B (Spec A) hX

/-- The universe lift of sheaves of `𝒪_étale`-modules into the module universe of the internal
Hom. -/
abbrev Up : Mod A B hX ⥤ SheafOfModules.{u + 1} (O A B hX) :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u} (O A B hX)

variable {A B hX} (P I : CochainComplex (ModuleCat.{u} A) ℤ) (J : CochainComplex (Mod A B hX) ℤ)

/-- `ε^* P̃`, degreewise. -/
abbrev Fc : CochainComplex (Mod A B hX) ℤ :=
  ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The internal Hom complex `SheafHom^•(ε^* P̃, J)`. -/
abbrev Tc : CochainComplex (SheafOfModules.{u + 1} (O A B hX)) ℤ :=
  (RingedSite.sheafHomComplex (Xs A B hX) (Fc (B := B) (hX := hX) P) J).obj

/-- The sections of each term of the internal Hom complex are `u`-small. -/
instance small_Tc (n : ℤ) (Y : (Site A B hX)ᵒᵖ) : Small.{u} (((Tc P J).X n).val.obj Y) :=
  RingedSite.small_sheafHomComplex_obj (Xs A B hX) _ _ n Y

/-- The `u`-small model of the degree-`n` term of the internal Hom complex. -/
abbrev Tsmall (n : ℤ) : Mod A B hX :=
  Stacks.SheafOfModules.sheafShrink.{u, u + 1} (O A B hX) ((Tc P J).X n)

/-- The `A`-module complex `Hom^•_A(P, I)`. -/
abbrev Dc : CochainComplex (ModuleCat.{u} A) ℤ := CochainComplex.HomComplexR A P I

variable {P I J} (ι : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
include ι

/-- The cochain `ι ∘ ε^*T(d) : ε^* P̃ ⟶ J[n]` attached to a cochain `d : P ⟶ I[n]`. -/
def globalCochain {n : ℤ} (d : Cochain P I n) : Cochain (Fc (B := B) (hX := hX) P) J n :=
  (d.map (epsT A B hX)).comp (Cochain.ofHom ι) (add_zero n)

/-- The components of `globalCochain ι d` are `ε^*T(d^{p,q}) ≫ ι^q`. -/
lemma globalCochain_v {n : ℤ} (d : Cochain P I n) (p q : ℤ) (hpq : p + n = q) :
    (globalCochain ι d).v p q hpq = (epsT A B hX).map (d.v p q hpq) ≫ ι.f q := by
  simp [globalCochain, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.map_v]

/-- The cochain `ι ∘ ε^*T(d)`, restricted to the slice over `⊤`. -/
def topCochain {n : ℤ} (d : Cochain P I n) :
    Cochain (RingedSite.restrictComplex (Xs A B hX) (Fc P) (top A B hX))
      (RingedSite.restrictComplex (Xs A B hX) J (top A B hX)) n :=
  (globalCochain ι d).map (SheafOfModules.overFunctor (O A B hX) (top A B hX))

/-- The components of `topCochain ι d` are the restrictions to `⊤` of
`ε^*T(d^{p,q}) ≫ ι^q`. -/
lemma topCochain_v {n : ℤ} (d : Cochain P I n) (p q : ℤ) (hpq : p + n = q) :
    (topCochain ι d).v p q hpq = (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map
      ((epsT A B hX).map (d.v p q hpq) ≫ ι.f q) :=
  congrArg (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map (globalCochain_v ι d p q hpq)

/-- The section over `⊤` of the internal Hom complex attached to a cochain `d : P ⟶ I[n]`. -/
def topSection {n : ℤ} (d : Cochain P I n) : ((Tc P J).X n).val.obj (op (top A B hX)) :=
  (((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)).inv.f n)
    (topCochain ι d)

/-- Under the identification of sections over `⊤` with cochains on the slice over `⊤`,
`topSection ι d` corresponds to `topCochain ι d`. -/
lemma sectionsIso_hom_topSection {n : ℤ} (d : Cochain P I n) :
    (((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)).hom.f n)
      (topSection ι d) = topCochain ι d := by
  change ((((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)).inv.f n) ≫
    (((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)).hom.f n))
      (topCochain ι d) = _
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id]
  rfl

omit ι in
/-- Precomposing with `ε^*T(a • h)` is multiplication by `ρ(a)` after precomposing with
`ε^*T h`. -/
lemma epsT_map_smul_comp_apply {M N : ModuleCat.{u} A} {E : Mod A B hX} (h : M ⟶ N)
    (g : (epsT A B hX).obj N ⟶ E) (a : A) (W : Site A B hX)
    (x : ((epsT A B hX).obj M).val.obj (op W)) :
    ((epsT A B hX).map (a • h) ≫ g).val.app (op W) x =
      (O A B hX).obj.map (toTop A B hX W).op (ρtop A B hX a) •
        ((epsT A B hX).map h ≫ g).val.app (op W) x := by
  rw [epsT_map_smul, Category.assoc, smulEnd_naturality, ← Category.assoc]
  rfl

/-- `topCochain ι` is additive in the cochain. -/
lemma topCochain_add {n : ℤ} (d d' : Cochain P I n) :
    topCochain ι (d + d') = topCochain ι d + topCochain ι d' := by
  rw [topCochain, topCochain, topCochain, globalCochain, globalCochain, globalCochain,
    Cochain.map_add, Cochain.add_comp, Cochain.map_add]

/-- `topSection ι` is additive in the cochain. -/
lemma topSection_add {n : ℤ} (d d' : Cochain P I n) :
    topSection ι (d + d') = topSection ι d + topSection ι d' :=
  (congrArg (((RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso
    (top A B hX)).inv.f n).hom (topCochain_add ι d d')).trans (map_add _ _ _)

/-- **The section attached to a cochain is `A`-linear in the cochain.** -/
lemma topSection_smul {n : ℤ} (a : A) (d : Cochain P I n) :
    topSection ι (a • d) = ρtop A B hX a • topSection ι d := by
  apply (ConcreteCategory.bijective_of_isIso (((RingedSite.sheafHomComplex (Xs A B hX) (Fc P)
    J).sectionsIso (top A B hX)).hom.f n)).1
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  apply SheafOfModules.hom_ext
  ext ⟨W⟩ x
  obtain ⟨W, ⟨⟨⟩⟩, f⟩ := W
  have hs := (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).smul_natural (top A B hX)
    (ρtop A B hX a) n p q hpq (topSection ι d) f x
  refine Eq.trans ?_ hs.symm
  have hBC := fun e : Cochain P I n => (congrArg
    (fun z => (((z.v p q hpq).val.app (op (Over.mk f))) x))
    (sectionsIso_hom_topSection ι e)).trans (congrArg
    (fun z => ((z.val.app (op (Over.mk f))) x)) (topCochain_v ι e p q hpq))
  let x' : ((epsT A B hX).obj (P.X p)).val.obj (op W) := x
  have hk := epsT_map_smul_comp_apply (d.v p q hpq) (ι.f q) a W x'
  have hf : toTop A B hX W = f := (toTop_eq A B hX f).symm
  rw [hf] at hk
  have hk' : ((epsT A B hX).map ((a • d).v p q hpq) ≫ ι.f q).val.app (op W) x' =
      (O A B hX).obj.map f.op (ρtop A B hX a) •
        ((epsT A B hX).map (d.v p q hpq) ≫ ι.f q).val.app (op W) x' := by
    rw [Cochain.smul_v]
    exact hk
  exact (hBC (a • d)).trans (hk'.trans (congrArg (fun (y : (J.X q).val.obj (op W)) =>
    (O A B hX).obj.map f.op (ρtop A B hX a) • y) (hBC d)).symm)

/-- `globalCochain ι` commutes with the differentials of the Hom complexes. -/
lemma globalCochain_δ {n m : ℤ} (d : Cochain P I n) :
    globalCochain ι (δ n m d) = δ n m (globalCochain ι d) := by
  rw [globalCochain, globalCochain, δ_comp_ofHom, δ_map]

/-- `topCochain ι` commutes with the differentials of the Hom complexes. -/
lemma topCochain_δ {n m : ℤ} (d : Cochain P I n) :
    topCochain ι (δ n m d) = δ n m (topCochain ι d) := by
  rw [topCochain, topCochain, globalCochain_δ, δ_map]

/-- The section attached to a cochain is compatible with the differentials. -/
lemma topSection_δ {n m : ℤ} (d : Cochain P I n) :
    ((Tc P J).d n m).val.app (op (top A B hX)) (topSection ι d) = topSection ι (δ n m d) := by
  let e := (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso (top A B hX)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.f m)).1
  have h := congrArg (fun g => g (topSection ι d)) (congrArg ConcreteCategory.hom (e.hom.comm n m))
  refine h.symm.trans ?_
  change ((CochainComplex.HomComplex _ _).d n m) (e.hom.f n (topSection ι d)) = _
  rw [sectionsIso_hom_topSection, sectionsIso_hom_topSection, topCochain_δ]
  rfl

/-! ### The comparison map -/

omit ι in
/-- The canonical global sections are natural in the module. -/
lemma unitSection_naturality {M M' : ModuleCat.{u} A} (f : M ⟶ M') (m : M) :
    ((epsT A B hX).map f).val.app (op (top A B hX)) (unitSection A B hX M m) =
      unitSection A B hX M' (f m) :=
  (congrArg (fun h => h.hom m) ((epsTAdj A B hX).unit.naturality f)).symm

omit ι in
/-- **A morphism out of the universe lift of `ε^*T M` into a sheaf with small sections is
determined by the images of the canonical global sections.** -/
lemma up_hom_ext {M : ModuleCat.{u} A} {S : SheafOfModules.{u + 1} (O A B hX)}
    [∀ Y, Small.{u} (S.val.obj Y)] (f g : (Up A B hX).obj ((epsT A B hX).obj M) ⟶ S)
    (h : ∀ m : M, f.val.app (op (top A B hX)) (ULift.up (unitSection A B hX M m)) =
      g.val.app (op (top A B hX)) (ULift.up (unitSection A B hX M m))) : f = g := by
  let e := Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (O A B hX) S
  let ff := Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} (O A B hX)
  have key : ∀ k : (Up A B hX).obj ((epsT A B hX).obj M) ⟶ S,
      k = (Up A B hX).map (ff.preimage (k ≫ e.inv)) ≫ e.hom := fun k => by
    rw [ff.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
  suffices hfg : ff.preimage (f ≫ e.inv) = ff.preimage (g ≫ e.inv) from
    (key f).trans ((congrArg (fun k => (Up A B hX).map k ≫ e.hom) hfg).trans (key g).symm)
  apply ((epsTAdj A B hX).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext m
  apply (Shrink.addEquiv (α := S.val.obj (op (top A B hX)))).injective
  have h1 := fun k => congrArg (fun k : (Up A B hX).obj ((epsT A B hX).obj M) ⟶ S =>
    k.val.app (op (top A B hX)) (ULift.up (unitSection A B hX M m))) (key k)
  exact (h1 f).symm.trans ((h m).trans (h1 g))

/-- The `A`-linear map `Hom^n_A(P, I) ⟶ Γ(Tsmall n)` attached to `ι`. -/
def sigmaMap (n : ℤ) : (Dc P I).X n ⟶ (gammaTop A B hX).obj (Tsmall (P := P) (J := J) n) :=
  ModuleCat.ofHom (X := (Dc P I).X n) (Y := (gammaTop A B hX).obj (Tsmall (P := P) (J := J) n))
    { toFun := fun d => (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm
        (topSection ι (d : Cochain P I n))
      map_add' := fun d d' =>
        (congrArg (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm
          (topSection_add ι d d')).trans (map_add _ _ _)
      map_smul' := fun a d => by
        change (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm
            (topSection ι (a • (d : Cochain P I n))) =
          ρtop A B hX a • (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm
            (topSection ι (d : Cochain P I n))
        exact (congrArg (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm
          (topSection_smul ι a d)).trans
          (map_smul (Shrink.linearEquiv ((O A B hX).obj.obj (op (top A B hX)))
            (((Tc P J).X n).val.obj (op (top A B hX)))).symm _ _) }

/-- `sigmaMap ι n` sends a cochain `d` to the shrunk section `topSection ι d`. -/
lemma sigmaMap_apply (n : ℤ) (d : Cochain P I n) :
    (sigmaMap ι n).hom d =
      (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm (topSection ι d) :=
  rfl

/-- The degree-`n` component of the comparison map, at module universe `u`. -/
def phiSmall (n : ℤ) : (epsT A B hX).obj ((Dc P I).X n) ⟶ Tsmall (P := P) (J := J) n :=
  ((epsTAdj A B hX).homEquiv _ _).symm (sigmaMap ι n)

/-- The degree-`n` component of the comparison map. -/
def phiN (n : ℤ) : (Up A B hX).obj ((epsT A B hX).obj ((Dc P I).X n)) ⟶ (Tc P J).X n :=
  (Up A B hX).map (phiSmall ι n) ≫
    (Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (O A B hX) ((Tc P J).X n)).hom

/-- **The comparison map sends the canonical global section attached to a cochain `d` to the
section of the internal Hom complex attached to `ι ∘ ε^*T(d)`.** -/
lemma phiN_app_top (n : ℤ) (d : Cochain P I n) :
    (phiN ι n).val.app (op (top A B hX))
        (ULift.up (unitSection A B hX ((Dc P I).X n) d)) = topSection ι d := by
  have h : (phiSmall ι n).val.app (op (top A B hX)) (unitSection A B hX ((Dc P I).X n) d) =
      (Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))).symm (topSection ι d) := by
    have := congrArg (fun g => g.hom d)
      (((epsTAdj A B hX).homEquiv _ _).apply_symm_apply (sigmaMap ι n))
    rw [Adjunction.homEquiv_unit] at this
    exact this.trans (sigmaMap_apply ι n d)
  change Shrink.addEquiv (α := ((Tc P J).X n).val.obj (op (top A B hX)))
    ((phiSmall ι n).val.app (op (top A B hX))
    (unitSection A B hX ((Dc P I).X n) d)) = _
  rw [h, AddEquiv.apply_symm_apply]

/-- **The comparison map**
`(ε^* Hom^•_A(P, I)~)^{lift} ⟶ SheafHom^•(ε^* P̃, J)`. -/
def compMap :
    ((Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj (Dc P I)) ⟶ Tc P J where
  f n := phiN ι n
  comm' n m _ := by
    apply up_hom_ext
    intro d
    have h1 := phiN_app_top (P := P) ι m (δ n m (d : Cochain P I n))
    have h2 := phiN_app_top (P := P) ι n (d : Cochain P I n)
    have h3 := unitSection_naturality (B := B) (hX := hX) ((Dc P I).d n m) d
    have h4 := topSection_δ (P := P) ι (m := m) (d : Cochain P I n)
    refine (congrArg (((Tc P J).d n m).val.app (op (top A B hX))) h2).trans ?_
    refine h4.trans ?_
    refine h1.symm.trans ?_
    exact congrArg (fun y => (phiN ι m).val.app (op (top A B hX)) (ULift.up y)) h3.symm

/-- The degree-`n` component of `compMap ι` is `phiN ι n`. -/
lemma compMap_f (n : ℤ) : (compMap (P := P) ι).f n = phiN (P := P) ι n := rfl

end AlgebraicGeometry.AffineEtaleDuality

end
