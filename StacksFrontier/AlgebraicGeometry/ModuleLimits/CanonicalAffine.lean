module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismLimit

/-!
# The canonical identification in the base change of sections over affine schemes

For a morphism `f : Y ⟶ X` of affine schemes and a quasi-coherent `𝒪_X`-module `F`, the global
sections of `f^*F` are the base change of the global sections of `F` along `f` on global
sections, by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.  This file records the
*coherence* of those identifications for a composite `q ≫ g = pi` of morphisms of affine
schemes: through them, the canonical comparison
`q^*(g^*F) ≅ pi^*F` of `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` becomes the cancellation of the intermediate
ring in an iterated base change, `Stacks.ModuleCat.cancelIsoApp`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.bcTop`: the base-change comparison for the global
  sections of a pullback along a morphism of affine schemes.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom`: the canonical identification
  `q^*(g^*F) ⟶ pi^*F` attached to an equation `q ≫ g = pi`, i.e. the morphism the conclusion of
  [Stacks Project, Tag 01ZR] (2) is stated with.
* `Stacks.AlgebraicGeometry.ModuleLimits.appTopHom`: a morphism of sheaves of modules read on
  global sections, as a map of modules over the ring of global sections.
* `Stacks.AlgebraicGeometry.ModuleLimits.xiTop`: the comparison of the global sections of an
  iterated pullback with the iterated base change.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_app_top_pullbackSection`: `canHom` carries the
  twice-pulled-back section to the section pulled back along the composite.  This holds for
  arbitrary schemes and is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` followed by
  `pullbackSection_congr`.
* `Stacks.AlgebraicGeometry.ModuleLimits.bc_can_coherence`: **the coherence.** On global
  sections over affine schemes, `canHom` is `Stacks.ModuleCat.cancelIsoApp`.
* `Stacks.AlgebraicGeometry.ModuleLimits.xiTop_comp_canHom`: the same, stated through the
  comparison `xiTop` of the sections of the iterated pullback with the iterated base change.

## Implementation notes

The coherence is proved by `ModuleCat.ExtendScalars.hom_ext`: two morphisms out of a base change
`S ⊗_R M` agree as soon as they agree on the elements `1 ⊗ m`.  Each of the four isomorphisms
involved has its value on such an element recorded —
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` for the three base changes and
`Stacks.ModuleCat.cancelIsoApp_hom_one_tmul` for the cancellation — so the whole coherence
reduces to `pullbackSection_comp` and `pullbackSection_congr` and no semilinearity or spanning
argument is needed.  The cancellation isomorphism is moved to the source side of the equation
first (`CategoryTheory.Iso.inv_comp_eq`) precisely so that the single application of
`ExtendScalars.hom_ext` is over the base ring `Γ(X, ⊤)` rather than over the intermediate one.

The inclusion `⊤ ≤ f ⁻¹ᵁ ⊤` is `Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top`
and the identification of `f.appLE ⊤ ⊤ _` with `AlgebraicGeometry.Scheme.Hom.appTop` is
`Stacks.AlgebraicGeometry.PicardBaseChange.appLE_top_top`.

The ring maps are spelled `AlgebraicGeometry.Scheme.Hom.appTop` throughout, although
`affinePullbackSectionsBaseChangeIso` presents them as `f.appLE ⊤ ⊤ _`: the two are *equal*
(`Stacks.AlgebraicGeometry.PicardBaseChange.appLE_top_top`) but not definitionally so, and
`appLE ⊤ ⊤ _` is the wrong spelling for the consumer, because the algebra structures that
`Stacks.RingFilteredColimits.exists_descend_rTensor` takes as instance arguments are the ones
induced by `appTop`.  Keeping both spellings in play makes the comparison of the two induced
module structures exceed the recursion limit, so `bcTop` transports the comparison to the
`appTop` spelling once, through `extendScalars_eqRec_hom_one_tmul`, which is stated at an
abstract module so that the transport costs nothing.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Stacks.ModuleCat Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.AlgebraicGeometry.PicardBaseChange (appLE_top_top)

/-! ### Global sections of a pullback as a base change -/

/-- Transporting an isomorphism out of a base change along an equality of ring maps does not
change its value on the elements `1 ⊗ₜ m`.  Stated at an abstract module so that it applies
without unfolding anything concrete. -/
theorem extendScalars_eqRec_hom_one_tmul {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (h : φ = ψ) {P : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (e : (ModuleCat.extendScalars φ).obj P ≅ N) (m : P) :
    (h ▸ e).hom ((1 : B) ⊗ₜ[A,ψ] m) = e.hom ((1 : B) ⊗ₜ[A,φ] m) := by
  subst h; rfl

/-- The global sections of the pullback of a quasi-coherent module along a morphism of affine
schemes are the base change of its global sections. -/
noncomputable def bcTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (ModuleCat.extendScalars (Scheme.Hom.appTop f).hom).obj
        (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤)) ≅
      ModuleCat.of Γ(Y, ⊤) ↑Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  (congrArg CommRingCat.Hom.hom (appLE_top_top f)) ▸
    affinePullbackSectionsBaseChangeIso f F (isAffineOpen_top X) (isAffineOpen_top Y)
      (le_preimage_top f ⊤)

/-- `bcTop` sends `1 ⊗ a` to the pullback of the section `a`. -/
theorem bcTop_hom_one_tmul {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] (a : Γ(F, ⊤)) :
    (bcTop f F).hom ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X,⊤), (Scheme.Hom.appTop f).hom] a) =
      Scheme.Modules.pullbackSection f F ⊤ ⊤ (le_preimage_top f ⊤) a := by
  have h1 := extendScalars_eqRec_hom_one_tmul (congrArg CommRingCat.Hom.hom (appLE_top_top f))
    (affinePullbackSectionsBaseChangeIso f F (isAffineOpen_top X) (isAffineOpen_top Y)
      (le_preimage_top f ⊤)) a
  have h2 := affinePullbackSectionsBaseChangeIso_one_tmul f F (isAffineOpen_top X)
    (isAffineOpen_top Y) (le_preimage_top f ⊤) a
  exact h1.trans h2

/-! ### Cancelling the intermediate ring on `1 ⊗ 1 ⊗ m` -/

/-- The inverse of `Stacks.ModuleCat.cancelIsoApp` sends `1 ⊗ₜ m` to `1 ⊗ₜ (1 ⊗ₜ m)`. -/
theorem cancelIsoApp_inv_one_tmul {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    (a : A →+* B) (b : B →+* R) (p : A →+* R) (hp : ∀ x, p x = b (a x)) (P : ModuleCat.{u} A)
    (m : P) (y : (ModuleCat.extendScalars a).obj P) (hy : y = (1 : B) ⊗ₜ[A,a] m) :
    (cancelIsoApp a b p hp P).inv ((1 : R) ⊗ₜ[A,p] m) = (1 : R) ⊗ₜ[B,b] y := by
  let _ : Algebra A B := a.toAlgebra
  let _ : Algebra A R := p.toAlgebra
  let fAlg : B →ₐ[A] R := { b with commutes' := fun r => (hp r).symm }
  have hhom : (cancelIsoApp a b p hp P).hom ((1 : R) ⊗ₜ[B,b] y) = (1 : R) ⊗ₜ[A,p] m := by
    refine (cancelIsoApp_hom_one_tmul a b p hp P fAlg (fun _ => rfl) y).trans ?_
    rw [hy]
    show fAlg (1 : B) ⊗ₜ[A,p] m = _
    rw [map_one]
  have hinv : ∀ z, (cancelIsoApp a b p hp P).inv ((cancelIsoApp a b p hp P).hom z) = z :=
    fun z => congrArg (fun k => (ConcreteCategory.hom k) z)
      (cancelIsoApp a b p hp P).hom_inv_id
  exact (congrArg (ConcreteCategory.hom (cancelIsoApp a b p hp P).inv) hhom).symm.trans (hinv _)

/-- `cancelIsoApp_inv_one_tmul` with both elements presented as variables together with
equations.  Only in this form can it be used by `rw`: the two sides of each equation are
definitionally but not syntactically of the type the surrounding application expects, so a
rewrite that inserts the explicit tensor into an application produces a term `rw` cannot
typecheck. -/
theorem cancelIsoApp_inv_eq {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    (a : A →+* B) (b : B →+* R) (p : A →+* R) (hp : ∀ x, p x = b (a x)) (P : ModuleCat.{u} A)
    (m : P) (x : (ModuleCat.extendScalars p).obj P) (hx : x = (1 : R) ⊗ₜ[A,p] m)
    (y : (ModuleCat.extendScalars a).obj P) (hy : y = (1 : B) ⊗ₜ[A,a] m)
    (w : (ModuleCat.extendScalars b).obj ((ModuleCat.extendScalars a).obj P))
    (hw : w = (1 : R) ⊗ₜ[B,b] y) :
    (cancelIsoApp a b p hp P).inv x = w := by
  subst hx; subst hw
  exact cancelIsoApp_inv_one_tmul a b p hp P m y hy

/-- `ModuleCat.ExtendScalars.map_tmul` with both elements presented as variables. -/
theorem extendScalars_map_eq {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M N : ModuleCat.{u} A} (h : M ⟶ N) (m : M)
    (x : (ModuleCat.extendScalars f).obj M) (hx : x = (1 : B) ⊗ₜ[A,f] m)
    (y : (ModuleCat.extendScalars f).obj N) (hy : y = (1 : B) ⊗ₜ[A,f] h m) :
    (ModuleCat.extendScalars f).map h x = y := by
  subst hx; subst hy
  exact ModuleCat.ExtendScalars.map_tmul f h 1 m

/-- An isomorphism out of a base change, applied to an element presented as a variable together
with an equation.  Stated for an abstract module, because the equation
`x = 1 ⊗ₜ m` cannot be elaborated at a concrete module of sections — the comparison of the
variable's type with the type of the explicit tensor unfolds `ModuleCat.extendScalars` on a
concrete argument and exceeds the recursion limit. -/
theorem extendScalars_iso_hom_eq {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    {P : ModuleCat.{u} A} {N : ModuleCat.{u} B} (e : (ModuleCat.extendScalars f).obj P ≅ N)
    {m : P} {t : N} (ht : e.hom ((1 : B) ⊗ₜ[A,f] m) = t)
    {x : (ModuleCat.extendScalars f).obj P} (hx : x = (1 : B) ⊗ₜ[A,f] m) :
    e.hom x = t :=
  (congrArg (ConcreteCategory.hom e.hom) hx).trans ht

/-- `ModuleCat.ExtendScalars.hom_ext` with the element `1 ⊗ₜ m` presented as a variable
together with an equation.  That is what makes it usable: the spelling of `1 ⊗ₜ m` produced by
Mathlib's statement is only definitionally the spelling a caller writes, so `rw` cannot abstract
over it; introducing it as a variable and substituting the caller's spelling repairs that. -/
theorem extendScalars_hom_ext' {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    {α β : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M) (x : (ModuleCat.extendScalars f).obj M),
      x = (1 : B) ⊗ₜ[A,f] m → α x = β x) : α = β :=
  ModuleCat.ExtendScalars.hom_ext (fun m => h m _ rfl)

/-! ### A morphism read on global sections -/

/-- A morphism of sheaves of modules read on global sections, as a map of modules over the ring
of global sections. -/
noncomputable def appTopHom {Y : Scheme.{u}} {A B : Y.Modules} (χ : A ⟶ B) :
    ModuleCat.of Γ(Y, ⊤) ↑Γ(A, ⊤) ⟶ ModuleCat.of Γ(Y, ⊤) ↑Γ(B, ⊤) :=
  ModuleCat.ofHom
    { toFun := fun a => χ.app ⊤ a
      map_add' := fun a b => map_add (ConcreteCategory.hom (χ.app ⊤)) a b
      map_smul' := fun r a => Scheme.Modules.Hom.app_smul χ r a }

/-- `appTopHom χ` sends a global section `a` to `χ.app ⊤ a`. -/
@[simp] theorem appTopHom_apply {Y : Scheme.{u}} {A B : Y.Modules} (χ : A ⟶ B) (a : Γ(A, ⊤)) :
    appTopHom χ a = χ.app ⊤ a := rfl

/-- `appTopHom` is compatible with composition of morphisms of sheaves of modules. -/
theorem appTopHom_comp {Y : Scheme.{u}} {A B C : Y.Modules} (χ : A ⟶ B) (χ' : B ⟶ C) :
    appTopHom (χ ≫ χ') = appTopHom χ ≫ appTopHom χ' := rfl

/-! ### The canonical identification -/

section Can

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
  (F : X.Modules)

/-- The canonical identification of the iterated pullback with the pullback of the composite:
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by `pullbackCongr`.  This is the
morphism the conclusion of [Stacks Project, Tag 01ZR] (2) is stated with. -/
noncomputable def canHom :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback pi).obj F :=
  (Scheme.Modules.pullbackComp q g).hom.app F ≫ (Scheme.Modules.pullbackCongr hpi).hom.app F

/-- The canonical identification is an isomorphism. -/
instance isIso_canHom : IsIso (canHom q g pi hpi F) := by
  rw [canHom]; infer_instance

/-- The canonical identification is natural in the module. -/
@[reassoc]
theorem canHom_naturality {M M' : X.Modules} (ψ : M ⟶ M') :
    (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map ψ) ≫
        canHom q g pi hpi M' = canHom q g pi hpi M ≫ (Scheme.Modules.pullback pi).map ψ := by
  have h1 : (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map ψ)
      = (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback q).map ψ := rfl
  unfold canHom
  rw [← Category.assoc, h1, (Scheme.Modules.pullbackComp q g).hom.naturality ψ,
    Category.assoc, (Scheme.Modules.pullbackCongr hpi).hom.naturality ψ, Category.assoc]

/-- The canonical identification carries the section pulled back twice to the section pulled
back along the composite. -/
theorem canHom_app_top_pullbackSection (a : Γ(F, ⊤)) :
    (canHom q g pi hpi F).app ⊤
        (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj F) ⊤ ⊤
          (le_preimage_top q ⊤)
          (Scheme.Modules.pullbackSection g F ⊤ ⊤ (le_preimage_top g ⊤) a))
      = Scheme.Modules.pullbackSection pi F ⊤ ⊤ (le_preimage_top pi ⊤) a := by
  have h1 := Scheme.Modules.pullbackSection_comp q g F ⊤ ⊤ ⊤ (le_preimage_top g ⊤)
    (le_preimage_top q ⊤) (hpi ▸ le_preimage_top pi ⊤) a
  have h2 := Scheme.Modules.pullbackSection_congr hpi F ⊤ ⊤ (hpi ▸ le_preimage_top pi ⊤)
    (le_preimage_top pi ⊤) a
  show ((Scheme.Modules.pullbackCongr hpi).hom.app F).val.app (op ⊤)
    (((Scheme.Modules.pullbackComp q g).hom.app F).val.app (op ⊤) _) = _
  rw [h1, h2]

end Can

/-! ### The coherence -/

section Coh

variable {W Z X : Scheme.{u}} [IsAffine W] [IsAffine Z] [IsAffine X]
  (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
  (F : X.Modules) [F.IsQuasicoherent]
  [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]

include hpi in
omit [IsAffine W] [IsAffine Z] [IsAffine X] in
/-- The three maps of global sections of a composite of morphisms of affine schemes form a
triangle. -/
theorem hp_triangle : ∀ x : Γ(X, ⊤),
    (Scheme.Hom.appTop pi).hom x
      = (Scheme.Hom.appTop q).hom ((Scheme.Hom.appTop g).hom x) := by
  intro x
  rw [← hpi, Scheme.Hom.comp_appTop]
  rfl

include hpi in
/-- **The coherence.** On global sections over affine schemes, the canonical identification of
the iterated pullback with the pullback of the composite is the cancellation of the intermediate
ring in the iterated base change. -/
theorem bc_can_coherence :
    (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map (bcTop g F).hom ≫
        (bcTop q ((Scheme.Modules.pullback g).obj F)).hom ≫
          appTopHom (canHom q g pi hpi F)
      = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
            (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤))).hom ≫ (bcTop pi F).hom := by
  set a := (Scheme.Hom.appTop g).hom with ha
  set b := (Scheme.Hom.appTop q).hom with hb
  set p := (Scheme.Hom.appTop pi).hom with hpp
  set hp := hp_triangle q g pi hpi with hhp
  set P := ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤) with hP
  rw [← Iso.inv_comp_eq]
  refine extendScalars_hom_ext' _ (fun m x hx => ?_)
  obtain ⟨y, hy⟩ : ∃ y : (ModuleCat.extendScalars a).obj P,
      y = (1 : Γ(Z, ⊤)) ⊗ₜ[Γ(X,⊤), a] m := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : (ModuleCat.extendScalars b).obj ((ModuleCat.extendScalars a).obj P),
      w = (1 : Γ(W, ⊤)) ⊗ₜ[Γ(Z,⊤), b] y := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : (ModuleCat.extendScalars b).obj
        (ModuleCat.of Γ(Z, ⊤) ↑Γ((Scheme.Modules.pullback g).obj F, ⊤)),
      v = (1 : Γ(W, ⊤)) ⊗ₜ[Γ(Z,⊤), b] ((bcTop g F).hom y) := ⟨_, rfl⟩
  iterate 3 refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  rw [cancelIsoApp_inv_eq a b p hp P m x hx y hy w hw,
    extendScalars_map_eq b (bcTop g F).hom y w hw v hv,
    extendScalars_iso_hom_eq (bcTop q ((Scheme.Modules.pullback g).obj F))
      (bcTop_hom_one_tmul q ((Scheme.Modules.pullback g).obj F) ((bcTop g F).hom y)) hv,
    extendScalars_iso_hom_eq (bcTop g F) (bcTop_hom_one_tmul g F m) hy,
    extendScalars_iso_hom_eq (bcTop pi F) (bcTop_hom_one_tmul pi F m) hx]
  exact canHom_app_top_pullbackSection q g pi hpi F m


/-- The comparison of the sections of the iterated pullback with the iterated base change. -/
noncomputable def xiTop :
    (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).obj
        ((ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤))) ≅
      ModuleCat.of Γ(W, ⊤) ↑Γ((Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback g).obj F), ⊤) :=
  (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).mapIso (bcTop g F) ≪≫
    bcTop q ((Scheme.Modules.pullback g).obj F)

/-- The forward map of `xiTop q g F` is the base change along `q` of `bcTop g F` followed by
`bcTop q` of the pullback of `F` along `g`. -/
theorem xiTop_hom : (xiTop q g F).hom =
    (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map (bcTop g F).hom ≫
      (bcTop q ((Scheme.Modules.pullback g).obj F)).hom := rfl

include hpi in
/-- On global sections, `xiTop q g F` followed by `canHom q g pi hpi F` is the cancellation of
the intermediate ring followed by `bcTop pi F`. -/
theorem xiTop_comp_canHom :
    (xiTop q g F).hom ≫ appTopHom (canHom q g pi hpi F)
      = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
            (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤))).hom ≫ (bcTop pi F).hom := by
  rw [xiTop_hom, Category.assoc]
  exact bc_can_coherence q g pi hpi F

end Coh

end Stacks.AlgebraicGeometry.ModuleLimits

end
