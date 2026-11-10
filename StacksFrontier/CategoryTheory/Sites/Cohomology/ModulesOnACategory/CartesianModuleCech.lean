module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparisonOnTheSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CoproductRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor

/-!
# Čech cohomology of a cartesian presheaf of modules

Let `O` be a presheaf of commutative rings on a category `C` and `P` a presheaf of `O`-modules
which is *cartesian*: for every morphism `g : Y ⟶ A` the restriction map induces an isomorphism
`O(Y) ⊗_{O(A)} P(A) ≅ P(Y)`. Over an object `A`, the rings `O(Y)` of the objects `Y` over `A`
are `O(A)`-algebras and the sections `P(Y)` are `O(A)`-modules; this file packages both as
functors on the slice at `A`, identifies the second with the base change of `P(A)` along the
first, and deduces the vanishing of positive Čech cohomology of Stacks 03FJ.

## Main definitions

* `Stacks.CartesianModuleCech.sliceAlgebras`: `Y ↦ O(Y)` as an algebra over `O(A)`.
* `Stacks.CartesianModuleCech.sliceModules`: `Y ↦ P(Y)` as an `O(A)`-module.
* `Stacks.CartesianModuleCech.amitsurIso`: for the base change presheaf, the second functor is
  the base change of `P(A)` along the first.

## Main results

* `Stacks.CartesianModuleCech.isZero_cechCohomology_succ`: **Stacks 03FJ for the base change
  presheaf**: its positive Čech cohomology vanishes on finite families with faithfully flat
  ring map, when the ring presheaf turns fibre products into pushouts.
-/

@[expose] public section

universe t v u r

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.TerminalBaseChange

namespace Stacks.CartesianModuleCech

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O] (A : C)

/-- The algebra structure on the ring of an object over `A`, over the universe lift of the ring
of `A`. -/
noncomputable abbrev sliceAlgebra (Y : Over A) :
    Algebra (ULift.{r} (O.obj (op A))) (O.obj (op Y.left)) :=
  ((O.map Y.hom.op).hom.comp (ULift.ringEquiv.toRingHom)).toAlgebra

/-- The ring of an object over `A`, as an algebra over the universe lift of the ring of `A`. -/
noncomputable def sliceAlgebraObj (Y : Over A) :
    CommAlgCat.{r} (ULift.{r} (O.obj (op A))) :=
  @CommAlgCat.of _ _ (O.obj (op Y.left)) _ (sliceAlgebra O A Y)

/-- **The rings of the objects over `A`, as algebras over the ring of `A`.** -/
noncomputable def sliceAlgebras :
    (Over A)ᵒᵖ ⥤ CommAlgCat.{r} (ULift.{r} (O.obj (op A))) where
  obj Y := sliceAlgebraObj O A Y.unop
  map {Y Y'} f :=
    CommAlgCat.ofHom (X := sliceAlgebraObj O A Y.unop) (Y := sliceAlgebraObj O A Y'.unop)
      { toRingHom := (O.map f.unop.left.op).hom
        commutes' := fun a => by
          change (O.map f.unop.left.op).hom ((O.map Y.unop.hom.op).hom a.down) =
            (O.map Y'.unop.hom.op).hom a.down
          rw [← RingCat.comp_apply, ← O.map_comp, ← op_comp, Over.w f.unop] }
  map_id Y := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    change (O.map (𝟙 Y.unop.left).op).hom a = a
    rw [op_id, O.map_id]
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    change (O.map (g.unop.left ≫ f.unop.left).op).hom a =
      (O.map g.unop.left.op).hom ((O.map f.unop.left.op).hom a)
    rw [op_comp, O.map_comp]
    rfl

variable {O A}

/-- **The sections of a presheaf of modules over the objects over `A`, as modules over the ring
of `A`.** -/
noncomputable abbrev sliceModules (P : PresheafOfModules.{t} O) :
    (Over A)ᵒᵖ ⥤ ModuleCat.{t} (O.obj (op A)) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 A))) Over.mkIdTerminal.op).obj
    ((PresheafOfModules.pushforward₀ (Over.forget A) O).obj P)

/-- The underlying abelian groups of `sliceModules` are the sections of the presheaf. -/
noncomputable def sliceModulesForgetIso (P : PresheafOfModules.{t} O) :
    (Over.forget A).op ⋙ P.presheaf ≅
      sliceModules (A := A) P ⋙ forget₂ (ModuleCat.{t} (O.obj (op A))) AddCommGrpCat.{t} :=
  NatIso.ofComponents (fun Y => Iso.refl (P.presheaf.obj (op Y.unop.left))) (fun _ => rfl)

section ULiftBaseChange

variable (R : Type r) [CommRing R] (B : Type r) [CommRing B] [Algebra R B]
  (N : Type t) [AddCommGroup N] [Module R N]

/-- An algebra over a ring is an algebra over its universe lift. -/
noncomputable abbrev uliftAlgebra : Algebra (ULift.{r} R) B :=
  ((algebraMap R B).comp ULift.ringEquiv.toRingHom).toAlgebra

/-- **Tensoring over the universe lift of a ring is tensoring over the ring.** -/
noncomputable def uliftTensorEquiv :
    letI := uliftAlgebra R B
    B ⊗[ULift.{r} R] N ≃ₗ[R] B ⊗[R] N := by
  letI := uliftAlgebra R B
  have hsmul : ∀ (a : ULift.{r} R) (x : B), a • x = a.down • x := fun _ _ => rfl
  haveI : SMulCommClass R (ULift.{r} R) B := ⟨fun a b x => by rw [hsmul, hsmul, smul_comm]⟩
  haveI : TensorProduct.CompatibleSMul R (ULift.{r} R) B N :=
    ⟨fun a x n => TensorProduct.smul_tmul a.down x n⟩
  haveI : TensorProduct.CompatibleSMul (ULift.{r} R) R B N :=
    ⟨fun a x n => TensorProduct.smul_tmul (ULift.up a : ULift.{r} R) x n⟩
  exact TensorProduct.equivOfCompatibleSMul R (ULift.{r} R) R B N

/-- `uliftTensorEquiv` sends `x ⊗ n` to `x ⊗ n`. -/
@[simp]
lemma uliftTensorEquiv_tmul (x : B) (n : N) :
    letI := uliftAlgebra R B
    uliftTensorEquiv R B N (x ⊗ₜ[ULift.{r} R] n) = x ⊗ₜ[R] n := rfl

end ULiftBaseChange

section BaseChangePresheaf

variable {X : C} (hX : IsTerminal X) (M : ModuleCat.{max t r} (O.obj (op X)))

/-- **The sections of the base change presheaf over an object over `A` are the base change of
its sections over `A`**: `O(Y) ⊗_{O(A)} (O(A) ⊗_{O(X)} M) ≅ O(Y) ⊗_{O(X)} M`. -/
noncomputable def baseChangeSliceEquiv (Y : Over A) :
    letI : Algebra (O.obj (op A)) (O.obj (op Y.left)) := (O.map Y.hom.op).hom.toAlgebra
    O.obj (op Y.left) ⊗[O.obj (op A)]
        (((baseChangePresheaf.{t} O hX).obj M).obj (op A)) ≃ₗ[O.obj (op Y.left)]
      ((baseChangePresheaf.{t} O hX).obj M).obj (op Y.left) := by
  letI algXA : Algebra ((constRing O X).obj (op A)) ((commPresheaf O).obj (op A)) :=
    ((theta O hX).app (op A)).hom.toAlgebra
  letI algAY : Algebra ((commPresheaf O).obj (op A)) ((commPresheaf O).obj (op Y.left)) :=
    (O.map Y.hom.op).hom.toAlgebra
  letI algXY : Algebra ((constRing O X).obj (op A)) ((commPresheaf O).obj (op Y.left)) :=
    ((theta O hX).app (op Y.left)).hom.toAlgebra
  haveI : IsScalarTower ((constRing O X).obj (op A)) ((commPresheaf O).obj (op A))
      ((commPresheaf O).obj (op Y.left)) :=
    IsScalarTower.of_algebraMap_eq fun s => by
      change rho O hX (op Y.left) s = (O.map Y.hom.op).hom (rho O hX (op A) s)
      exact (rho_comp_apply O hX Y.hom.op s).symm
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange ((constRing O X).obj (op A))
    ((commPresheaf O).obj (op A)) ((commPresheaf O).obj (op Y.left))
    ((commPresheaf O).obj (op Y.left)) ((constModObj.{t} O X M).obj (op A))

/-- The component of the identification of the sections over the slice with the coefficients
of the Amitsur complex. -/
noncomputable def amitsurComponentEquiv (Y : Over A) :
    ((Stacks.Descent.amitsurCoefficients.{r, r, max t r} (O.obj (op A))
      (((baseChangePresheaf.{t} O hX).obj M).obj (op A))).obj
        ((sliceAlgebras O A).obj (op Y))) ≃ₗ[O.obj (op A)]
      ((sliceModules (A := A) ((baseChangePresheaf.{t} O hX).obj M)).obj (op Y)) := by
  letI algAY : Algebra (O.obj (op A)) (O.obj (op Y.left)) := (O.map Y.hom.op).hom.toAlgebra
  let e₁ := uliftTensorEquiv (O.obj (op A)) (O.obj (op Y.left))
    (((baseChangePresheaf.{t} O hX).obj M).obj (op A))
  let e₂ := baseChangeSliceEquiv (A := A) hX M Y
  refine
    { toFun := fun x => e₂ (e₁ x)
      invFun := fun y => e₁.symm (e₂.symm y)
      left_inv := fun x => (congrArg e₁.symm (e₂.symm_apply_apply _)).trans
        (e₁.symm_apply_apply x)
      right_inv := fun y => (congrArg e₂ (e₁.apply_symm_apply _)).trans (e₂.apply_symm_apply y)
      map_add' := fun x y => (congrArg e₂ (e₁.map_add x y)).trans (e₂.map_add _ _)
      map_smul' := fun c x => (congrArg e₂ (e₁.map_smul c x)).trans ?_ }
  have hto : (Over.mkIdTerminal (X := A)).from Y = Over.homMk Y.hom :=
    Over.mkIdTerminal.hom_ext _ _
  refine (congrArg e₂ ?_).trans ((e₂.map_smul ((O.map Y.hom.op).hom c) (e₁ x)).trans ?_)
  swap
  · change _ = (O.map (((Over.mkIdTerminal (X := A)).from Y).left).op).hom c • e₂ (e₁ x)
    rw [hto]
    rfl
  induction e₁ x using TensorProduct.inductionOn with
  | tmul b n => rfl
  | add y z hy hz => rw [smul_add, smul_add, hy, hz]

/-- The component sends `b ⊗ n` to `b` times the restriction of `n`. -/
lemma amitsurComponentEquiv_apply (Y : Over A) (b : (sliceAlgebras O A).obj (op Y))
    (n : ((baseChangePresheaf.{t} O hX).obj M).obj (op A)) :
    (amitsurComponentEquiv (A := A) hX M Y (b ⊗ₜ[ULift.{r} (O.obj (op A))] n) :
        ((baseChangePresheaf.{t} O hX).obj M).obj (op Y.left)) =
      (show O.obj (op Y.left) from b) •
        (show ((baseChangePresheaf.{t} O hX).obj M).obj (op Y.left) from
          ((baseChangePresheaf.{t} O hX).obj M).map Y.hom.op n) := by
  let φ : (((baseChangePresheaf.{t} O hX).obj M).obj (op A)) →+
      (((baseChangePresheaf.{t} O hX).obj M).obj (op Y.left)) :=
    (amitsurComponentEquiv (A := A) hX M Y).toLinearMap.toAddMonoidHom.comp
      (TensorProduct.mk (ULift.{r} (O.obj (op A))) _ _ b).toAddMonoidHom
  let ψ : (((baseChangePresheaf.{t} O hX).obj M).obj (op A)) →+
      (((baseChangePresheaf.{t} O hX).obj M).obj (op Y.left)) :=
    (DistribSMul.toAddMonoidHom _ (show O.obj (op Y.left) from b)).comp
      (((baseChangePresheaf.{t} O hX).obj M).map Y.hom.op).hom.toAddMonoidHom
  change φ n = ψ n
  induction n using TensorProduct.inductionOn with
  | add n₁ n₂ h₁ h₂ =>
    exact (map_add φ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (map_add ψ _ _).symm)
  | tmul a m =>
    let := ((theta O hX).app (op Y.left)).hom.toAlgebra
    exact congrArg (fun z => z ⊗ₜ[(constRing O X).obj (op Y.left)]
      (show (constModObj.{t} O X M).obj (op Y.left) from m)) (mul_comm _ _)

/-- **The sections of the base change presheaf over the slice at `A` are the coefficients of
the Amitsur complex of `O(A) ⟶ O(-)` with values in its sections over `A`.** -/
noncomputable def amitsurIso :
    sliceAlgebras O A ⋙ Stacks.Descent.amitsurCoefficients.{r, r, max t r} (O.obj (op A))
        (((baseChangePresheaf.{t} O hX).obj M).obj (op A)) ≅
      sliceModules (A := A) ((baseChangePresheaf.{t} O hX).obj M) :=
  NatIso.ofComponents (fun Y => (amitsurComponentEquiv (A := A) hX M Y.unop).toModuleIso) (by
    intro Y Y' f
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add _ _ _).symm)
    | tmul b n =>
      refine (amitsurComponentEquiv_apply (A := A) hX M Y'.unop
        ((O.map f.unop.left.op).hom b) n).trans ?_
      refine Eq.trans ?_ (congrArg (((sliceModules (A := A)
        ((baseChangePresheaf.{t} O hX).obj M)).map f).hom)
          (amitsurComponentEquiv_apply (A := A) hX M Y.unop b n)).symm
      refine Eq.trans ?_ (PresheafOfModules.map_smul _ f.unop.left.op _ _).symm
      refine congrArg ((O.map f.unop.left.op).hom b • ·) ?_
      refine Eq.trans ?_ (PresheafOfModules.map_comp_apply _ Y.unop.hom.op f.unop.left.op n)
      rw [← op_comp, Over.w f.unop])

end BaseChangePresheaf

section SliceAlgebraColimits

variable (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O] (A : C)

/-- **The ring of an object isomorphic over `A` to `A` is initial among algebras over the ring of
`A`.** -/
noncomputable def isInitialSliceAlgebraObj (Y : Over A) [IsIso Y.hom] :
    IsInitial (sliceAlgebraObj O A Y) := by
  letI := sliceAlgebra O A Y
  have hbij : Function.Bijective (algebraMap (ULift.{r} (O.obj (op A))) (O.obj (op Y.left))) :=
    (ConcreteCategory.bijective_of_isIso (O.map Y.hom.op)).comp ULift.ringEquiv.bijective
  exact IsInitial.ofIso CommAlgCat.isInitialSelf (CommAlgCat.isoMk
    (AlgEquiv.ofBijective (Algebra.ofId (ULift.{r} (O.obj (op A))) (O.obj (op Y.left))) hbij))

variable {O A}

/-- **A fibre product over `A` whose square of rings is a pushout has as ring the coproduct of
the algebras of the factors.** -/
noncomputable def isColimitSliceAlgebrasBinaryCofan {Y₁ Y₂ : Over A} (c : BinaryFan Y₁ Y₂)
    (hc : IsPushout (CommRingCat.ofHom (O.map Y₁.hom.op).hom)
      (CommRingCat.ofHom (O.map Y₂.hom.op).hom) (CommRingCat.ofHom (O.map c.fst.left.op).hom)
      (CommRingCat.ofHom (O.map c.snd.left.op).hom)) :
    IsColimit (BinaryCofan.mk ((sliceAlgebras O A).map c.fst.op)
      ((sliceAlgebras O A).map c.snd.op)) := by
  have hpt : (O.map c.pt.hom.op).hom =
      (O.map c.fst.left.op).hom.comp (O.map Y₁.hom.op).hom := by
    rw [← RingCat.hom_comp, ← O.map_comp, ← op_comp]
    exact congrArg (fun g => (O.map g.op).hom) (Over.w c.fst).symm
  refine BinaryCofan.IsColimit.mk _ (fun {Q} f₁ f₂ => ?_) ?_ ?_ ?_
  · refine CommAlgCat.ofHom (X := sliceAlgebraObj O A c.pt) (Y := Q)
      { toRingHom := (hc.desc (CommRingCat.ofHom (R := O.obj (op Y₁.left)) f₁.hom.toRingHom)
          (CommRingCat.ofHom (R := O.obj (op Y₂.left)) f₂.hom.toRingHom) ?_).hom
        commutes' := fun a => ?_ }
    · ext x
      exact (f₁.hom.commutes (ULift.up x)).trans (f₂.hom.commutes (ULift.up x)).symm
    · change (hc.desc _ _ _).hom ((O.map c.pt.hom.op).hom a.down) = _
      rw [hpt, RingHom.comp_apply, ← CommRingCat.ofHom_apply (O.map c.fst.left.op).hom,
        ← CommRingCat.comp_apply, hc.inl_desc]
      exact f₁.hom.commutes a
  · intro Q f₁ f₂
    ext x
    exact congrArg (fun φ : CommRingCat.of (O.obj (op Y₁.left)) ⟶ CommRingCat.of Q => φ.hom x)
      (hc.inl_desc _ _ _)
  · intro Q f₁ f₂
    ext x
    exact congrArg (fun φ : CommRingCat.of (O.obj (op Y₂.left)) ⟶ CommRingCat.of Q => φ.hom x)
      (hc.inr_desc _ _ _)
  · intro Q f₁ f₂ m h₁ h₂
    ext x
    have key := hc.hom_ext (W := CommRingCat.of Q)
      (k := CommRingCat.ofHom (R := O.obj (op c.pt.left)) m.hom.toRingHom)
      (l := hc.desc (CommRingCat.ofHom (R := O.obj (op Y₁.left)) f₁.hom.toRingHom)
        (CommRingCat.ofHom (R := O.obj (op Y₂.left)) f₂.hom.toRingHom) (by
          ext y
          exact (f₁.hom.commutes (ULift.up y)).trans (f₂.hom.commutes (ULift.up y)).symm))
      (CommRingCat.hom_ext ?_) (CommRingCat.hom_ext ?_)
    · exact congrArg (fun φ : CommRingCat.of (O.obj (op c.pt.left)) ⟶ CommRingCat.of Q =>
        φ.hom x) key
    · ext y
      exact (congrArg (fun φ => φ.hom y) h₁).trans
        (congrArg (fun φ : CommRingCat.of (O.obj (op Y₁.left)) ⟶ CommRingCat.of Q => φ.hom y)
          (hc.inl_desc (CommRingCat.ofHom (R := O.obj (op Y₁.left)) f₁.hom.toRingHom)
            (CommRingCat.ofHom (R := O.obj (op Y₂.left)) f₂.hom.toRingHom) _)).symm
    · ext y
      exact (congrArg (fun φ => φ.hom y) h₂).trans
        (congrArg (fun φ : CommRingCat.of (O.obj (op Y₂.left)) ⟶ CommRingCat.of Q => φ.hom y)
          (hc.inr_desc (CommRingCat.ofHom (R := O.obj (op Y₁.left)) f₁.hom.toRingHom)
            (CommRingCat.ofHom (R := O.obj (op Y₂.left)) f₂.hom.toRingHom) _)).symm

end SliceAlgebraColimits

section PowerSections

open Stacks.CechSite

variable {D : Type*} [Category D] [HasFiniteProducts D] (Y : D) {𝒜 : Type*} [Category 𝒜]
  (H : Dᵒᵖ ⥤ 𝒜) (n : SimplexCategory)

/-- **The sections of a power are a wide pushout when they are a coproduct over an initial
head.** If the sections of the terminal object are initial and the sections of `Y^{n+1}` are the
coproduct of the sections of its factors, the cocone of the projections is a wide pushout. -/
noncomputable def isColimitPowerSectionsCoconeOfIsInitial
    (hI : IsInitial (sectionsTerminalArrow Y H).left)
    (hc : IsColimit (Cofan.mk ((powerSections Y H).obj n) (powerSectionsIncl Y H n))) :
    IsColimit (powerSectionsCocone Y H n) where
  desc s := Cofan.IsColimit.desc hc (fun a => s.ι.app (some a))
  fac s j := by
    rcases j with _ | a
    · exact hI.hom_ext _ _
    · exact Cofan.IsColimit.fac hc _ a
  uniq s m hm := Cofan.IsColimit.hom_ext hc _ _ (fun a =>
    (hm (some a)).trans (Cofan.IsColimit.fac hc (fun a => s.ι.app (some a)) a).symm)

/-- **A presheaf turning finite products into coproducts turns a power into a coproduct.** -/
noncomputable def isColimitPowerCofanOfPreservesFiniteProducts
    [PreservesFiniteProducts H.rightOp] :
    IsColimit (Cofan.mk ((powerSections Y H).obj n) (powerSectionsIncl Y H n)) := by
  have hl := isLimitMapConeFanMkEquiv H.rightOp (fun _ : Fin (n.len + 1) => Y)
    (Pi.π (fun _ : Fin (n.len + 1) => Y))
    (isLimitOfPreserves H.rightOp (limit.isLimit (Discrete.functor fun _ : Fin (n.len + 1) => Y)))
  refine Cofan.IsColimit.mk _ (fun s => (hl.lift (Fan.mk (op s.pt) (fun a => (s.inj a).op))).unop)
    (fun s a => Quiver.Hom.op_inj (hl.fac (Fan.mk (op s.pt) (fun a => (s.inj a).op)) ⟨a⟩))
    (fun s m hm => Quiver.Hom.op_inj (Fan.IsLimit.hom_ext hl _ _ (fun a =>
      (congrArg Quiver.Hom.op (hm a)).trans
        (hl.fac (Fan.mk (op s.pt) (fun a => (s.inj a).op)) ⟨a⟩).symm)))

end PowerSections

section CechVanishing

open Stacks.CechSite Stacks.Descent AlgebraicTopology

variable [HasFiniteLimits C]

/-- **The algebras of a fibre product over `A` are the coproduct of the algebras of the
factors.** If every binary product over `A` has a pushout square of rings, the algebras of the
slice at `A` take finite products to coproducts. -/
theorem preservesFiniteProducts_sliceAlgebras_rightOp
    (hpush : ∀ {Y₁ Y₂ : Over A} (c : BinaryFan Y₁ Y₂), IsLimit c →
      IsPushout (CommRingCat.ofHom (O.map Y₁.hom.op).hom)
        (CommRingCat.ofHom (O.map Y₂.hom.op).hom) (CommRingCat.ofHom (O.map c.fst.left.op).hom)
        (CommRingCat.ofHom (O.map c.snd.left.op).hom)) :
    PreservesFiniteProducts (sliceAlgebras O A).rightOp := by
  have : ∀ Y₁ Y₂ : Over A, PreservesLimit (pair Y₁ Y₂) (sliceAlgebras O A).rightOp :=
    fun Y₁ Y₂ => preservesLimit_of_preserves_limit_cone (prodIsProd Y₁ Y₂)
      ((isLimitMapConeBinaryFanEquiv _ _ _).symm (BinaryCofan.IsColimit.op
        (isColimitSliceAlgebrasBinaryCofan _ (hpush _ (prodIsProd Y₁ Y₂)))))
  have : PreservesLimitsOfShape (Discrete WalkingPair) (sliceAlgebras O A).rightOp :=
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm⟩
  have : IsIso (Over.mk (𝟙 A)).hom := inferInstanceAs (IsIso (𝟙 A))
  have : PreservesLimit (Functor.empty.{0} (Over A)) (sliceAlgebras O A).rightOp :=
    preservesLimit_of_preserves_limit_cone (Over.mkIdTerminal (X := A))
      ((isLimitMapConeEmptyConeEquiv _ _).symm
        (terminalOpOfInitial (isInitialSliceAlgebraObj O A (Over.mk (𝟙 A)))))
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (sliceAlgebras O A).rightOp
  exact .of_preserves_binary_and_terminal _

/-- The structure morphism of the terminal object of the slice at `A` is an isomorphism. -/
instance isIso_terminal_hom : IsIso (⊤_ (Over A)).hom := by
  have h := Over.w (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := A))).hom
  rw [← h]
  have : IsIso (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := A))).hom.left :=
    Iso.isIso_hom ((Over.forget A).mapIso
      (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := A))))
  have : IsIso (Over.mk (𝟙 A)).hom := inferInstanceAs (IsIso (𝟙 A))
  infer_instance

variable (O A) in
/-- **The sections of the terminal arrow of the slice at `A` along `h : Z ⟶ A` are the algebra
map `O(A) → O(Z)`.** -/
noncomputable def sectionsTerminalArrowIso {Z : C} (h : Z ⟶ A) :
    letI := (O.map h.op).hom.toAlgebra
    sectionsTerminalArrow (Over.mk h) (sliceAlgebras O A) ≅
      algebraMapArrow (O.obj (op A)) (O.obj (op Z)) :=
  letI := (O.map h.op).hom.toAlgebra
  letI : Algebra (ULift.{r} (O.obj (op A))) (O.obj (op Z)) := sliceAlgebra O A (Over.mk h)
  Arrow.isoMk ((isInitialSliceAlgebraObj O A (⊤_ (Over A))).uniqueUpToIso
      CommAlgCat.isInitialSelf)
    (CommAlgCat.isoMk (X := O.obj (op Z)) (Y := ULift.{r} (O.obj (op Z)))
      { toRingEquiv := ULift.ringEquiv.symm
        commutes' := fun _ => rfl })
    ((isInitialSliceAlgebraObj O A (⊤_ (Over A))).hom_ext _ _)

variable {X : C} (hX : IsTerminal X) (M : ModuleCat.{r} (O.obj (op X)))

/-- **Stacks 03FJ for a one-member family, for the base change presheaf.** On a category with
finite limits whose ring presheaf turns fibre products into pushouts, the base change presheaf
`Y ↦ O(Y) ⊗_{O(X)} M` has vanishing positive Čech cohomology for every `h : Z ⟶ A` with
`O(A) → O(Z)` faithfully flat. -/
theorem isZero_cechCohomology_singleton_succ {Z : C} (h : Z ⟶ A)
    (hpush : ∀ {Y₁ Y₂ : Over A} (c : BinaryFan Y₁ Y₂), IsLimit c →
      IsPushout (CommRingCat.ofHom (O.map Y₁.hom.op).hom)
        (CommRingCat.ofHom (O.map Y₂.hom.op).hom) (CommRingCat.ofHom (O.map c.fst.left.op).hom)
        (CommRingCat.ofHom (O.map c.snd.left.op).hom))
    (hff : letI := (O.map h.op).hom.toAlgebra
      Module.FaithfullyFlat (O.obj (op A)) (O.obj (op Z))) (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{r} h)
      ((baseChangePresheaf.{r} O hX).obj M).presheaf (p + 1)) := by
  let := (O.map h.op).hom.toAlgebra
  have := hff
  have := preservesFiniteProducts_sliceAlgebras_rightOp hpush
  refine isZero_cechCohomology_of_isZero_sliceModule _ (O.obj (op A)) _
    (sliceModules (A := A) ((baseChangePresheaf.{r} O hX).obj M))
    (sliceModulesForgetIso _) (p + 1)
    (isZero_sliceCechCohomology_singleton_succ_of_powerSections h _ (sliceAlgebras O A)
      (Functor.isoWhiskerLeft (cechNerveTerminalFrom (Over.mk h)).rightOp
        (amitsurIso (A := A) hX M).symm)
      (sectionsTerminalArrowIso O A h)
      (fun n => isIso_conerveSectionsMap _ _ n
        (isColimitPowerSectionsCoconeOfIsInitial _ _ n
          (isInitialSliceAlgebraObj O A (⊤_ (Over A)))
          (isColimitPowerCofanOfPreservesFiniteProducts _ _ n))) p)

/-- **Stacks 03FJ for a finite family, for the base change presheaf.** On a finitary extensive
category with finite limits whose ring presheaf turns fibre products into pushouts, the base
change presheaf, if it takes finite coproducts to products, has vanishing positive Čech
cohomology for every finite family `{Yᵢ → A}` with `O(A) → O(∐ Yᵢ)` faithfully flat. -/
theorem isZero_cechCohomology_succ [FinitaryExtensive C] (E : PreZeroHypercover.{r} A)
    [Finite E.I₀] [PreservesFiniteProducts ((baseChangePresheaf.{r} O hX).obj M).presheaf]
    (hpush : ∀ {Y₁ Y₂ : Over A} (c : BinaryFan Y₁ Y₂), IsLimit c →
      IsPushout (CommRingCat.ofHom (O.map Y₁.hom.op).hom)
        (CommRingCat.ofHom (O.map Y₂.hom.op).hom) (CommRingCat.ofHom (O.map c.fst.left.op).hom)
        (CommRingCat.ofHom (O.map c.snd.left.op).hom))
    (hff : letI := (O.map (Sigma.desc E.f).op).hom.toAlgebra
      Module.FaithfullyFlat (O.obj (op A)) (O.obj (op (∐ E.X)))) (p : ℕ) :
    IsZero (cechCohomology E ((baseChangePresheaf.{r} O hX).obj M).presheaf (p + 1)) := by
  have := isIso_cechComplexMap_of_preservesFiniteProducts E
    ((baseChangePresheaf.{r} O hX).obj M).presheaf
  exact (isZero_cechCohomology_singleton_succ hX M (Sigma.desc E.f) hpush hff p).of_iso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (p + 1)).mapIso
      (asIso (cechComplexMap E (PreZeroHypercover.singleton.{r} (Sigma.desc E.f))
        (coproductRefinement E) ((baseChangePresheaf.{r} O hX).obj M).presheaf))).symm

end CechVanishing

end Stacks.CartesianModuleCech

end
