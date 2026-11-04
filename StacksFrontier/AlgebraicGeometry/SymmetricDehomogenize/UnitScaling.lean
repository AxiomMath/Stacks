module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.SymmetricDehomogenize.Basic

/-!
# Rescaling the trivialization of a quotient does not move the classified morphism

Let `g : X ⟶ T` be a morphism of schemes, `F` a module on `T` and `κ : F ⟶ g_*𝒪_X` a
trivialized quotient of `F` in the sense of
`StacksFrontier/AlgebraicGeometry/SymmetricDehomogenize/Basic.lean`. The dehomogenization
`Stacks.SymmetricDehomogenize.dehomogenize` turns `κ` into a ring map out of the graded ring of
homogeneous sections of `Sym F` over an open `U` of `T`, and that ring map classifies a morphism
to `Proj` of that graded ring.

**A trivialization is never canonical**: `κ` is built from an isomorphism of the quotient with
the structure sheaf, and two such isomorphisms differ by multiplication by a global unit `w` of
`X`. This file shows that the classified morphism does not see the difference.

The argument is the one of
[Stacks, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE): replacing `κ` by `w · κ` multiplies
the degree-`d` part of the dehomogenization by `wᵈ`, and
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` says that a
degreewise unit rescaling of a ring map to global sections leaves the morphism to `Proj` alone.

## Why the degreewise rescaling is a uniqueness argument and not a computation

`Stacks.SymmetricDehomogenize.gradedHom` is `desc` of `κ` for the universal property of the
symmetric algebra, so there is no formula for its degree-`n` component to rescale. What there is
instead is uniqueness: multiplication by `wⁿ` in degree `n` is a *unital homomorphism of graded
algebras* `g_*𝒪_X ⟶ g_*𝒪_X` — that is exactly the content of `pushforwardUnitScale` below, whose
`map_mul` field is `w^(i+j) = wⁱ · wʲ` — and composing `desc κ` with it is a unital homomorphism
extending `w · κ`. By `SheafOfModules.GradedAlgebra.IsUniversal.desc_unique` it *is* `desc (w · κ)`,
in every degree at once. This is `gradedHom_comp_pushforwardUnitMulBy`.

Negative degrees are the reason `w` is taken to be a unit rather than an arbitrary global
function: `pushforwardUnitGradedAlgebra` has `g_*𝒪_X` in every integer degree, so the family
`n ↦ wⁿ` must be defined for negative `n` as well. Nothing else uses invertibility — the
hypothesis of `fromOfGlobalSections_congr_unit` is about nonnegative degrees only.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.resPushforward`: restriction of a global
  function of `X` to `g⁻¹W`, as a ring homomorphism.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitMulBy`: multiplication by a
  global function of `X`, as an endomorphism of `g_*𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitScale`: the family of its
  powers, as a unital homomorphism of graded algebras of `g_*𝒪_X` with itself.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.globalOfUnitEnd`: the global function an
  endomorphism of `𝒪_X` multiplies by, and
  `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitOfUnitIso`: for an automorphism, the unit
  of `Γ(X, 𝒪)` it is.

## Main results

* `Stacks.SymmetricDehomogenize.gradedHom_comp_pushforwardUnitMulBy`: the graded map of `w · κ`
  is the graded map of `κ` followed by the scaling, in every degree.
* `Stacks.SymmetricDehomogenize.dehomogenize_pow_mul`: **the dehomogenization of `w · κ` is
  `uᵈ` times the dehomogenization of `κ` in degree `d`**, with `u` the image of `w`. This is the
  port to `Stacks.SymmetricDehomogenize.dehomogenize` of
  `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize_pow_mul`, and it is exactly the
  hypothesis `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` consumes.
* `Stacks.SymmetricDehomogenize.fromOfGlobalSections_dehomogenize_congr_mulBy`: **the morphism to
  `Proj` of the graded ring of sections is unchanged by the rescaling.**
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.eq_unitMulBy`: **every endomorphism of `𝒪_X`
  is multiplication by a global function**, and `globalOfUnitEnd_comp` says the function is
  multiplicative in the endomorphism. This is what identifies the difference between two
  trivializations of one invertible quotient as a unit, which is the `w` above.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pushforward` is a functor, so multiplication by `w` on `g_*𝒪_X`
is obtained by pushing forward multiplication by `w` on `𝒪_X`, and the latter is Mathlib's
`SheafOfModules.unitHomEquiv` — a morphism out of the unit sheaf of modules is the image of `1` —
applied to the compatible family of restrictions of `w`, which is
`Stacks.SheafOfModules.terminalSection`. Both steps are definitional on sections, so
`ofPushforwardUnit_pushforwardUnitMulBy_app` holds by `rfl`.

The rings `X.ringCatSheaf.obj.obj W` carry no `CommRing` instance that instance search can find —
they are `RingCat` objects obtained by forgetting commutativity — so the rearrangement
`(a · b) · (c · d) = (a · c) · (b · d)` cannot be `ring` and is `ringCatSheaf_mul_mul_mul_comm`
below, proved from `Stacks.SymGraded.isCommutativeRingSheaf_scheme`.

No `@[stacks]` attribute is attached. The invariance is registered where it is proved, on
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`; what is done here is to feed the
symmetric algebra's dehomogenization into it, which asserts no tag of its own. Tag 0B3V's
bijection is not reached.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

variable {X T : Scheme.{u}} (g : X ⟶ T)

/-- **The rearrangement `(a · b) · (c · d) = (a · c) · (b · d)`** in a ring of sections of the
structure sheaf. Mathlib's `mul_mul_mul_comm` is stated for a `CommMonoid`, and the `RingCat`
objects underlying a scheme's structure sheaf carry no commutativity instance that instance
search finds; `Stacks.SymGraded.isCommutativeRingSheaf_scheme` is the commutativity. -/
public theorem ringCatSheaf_mul_mul_mul_comm (W : X.Opensᵒᵖ)
    (a b c d : X.ringCatSheaf.obj.obj W) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc a b (c * d), ← mul_assoc b c d, isCommutativeRingSheaf_scheme X W b c,
    mul_assoc c b d, ← mul_assoc a c (b * d)]

/-- **Restriction of a global function of `X` to `g⁻¹W`**, as a ring homomorphism. This is the
scalar by which `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitMulBy` multiplies
the sections of `g_*𝒪_X` over `W`. -/
public def resPushforward (W : T.Opensᵒᵖ) :
    Γ(X, ⊤) →+* X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop)) :=
  (X.ringCatSheaf.obj.map (isTerminalTop.from (g ⁻¹ᵁ W.unop)).op).hom

/-- **Multiplication by a global function of `X`, as an endomorphism of `𝒪_X`.** A morphism out of
the unit sheaf of modules is the image of the unit section, by Mathlib's
`SheafOfModules.unitHomEquiv`; the section taken here is the compatible family of restrictions of
`w`. -/
public def unitMulBy (w : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
    (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop w)

/-- **Multiplication by a global function of `X`, as an endomorphism of `g_*𝒪_X`**: the
pushforward of `unitMulBy`. -/
public def pushforwardUnitMulBy (w : Γ(X, ⊤)) : pushforwardUnit g ⟶ pushforwardUnit g :=
  (Scheme.Modules.pushforward g).map (unitMulBy w)

/-- **On sections, `pushforwardUnitMulBy` is multiplication by the restriction of `w`.** Every
step of the construction is definitional on sections, so this is `rfl`. -/
@[simp]
public theorem ofPushforwardUnit_pushforwardUnitMulBy_app (w : Γ(X, ⊤)) (W : T.Opensᵒᵖ)
    (x : (pushforwardUnit g).val.obj W) :
    ofPushforwardUnit g ((pushforwardUnitMulBy g w).val.app W x) =
      ofPushforwardUnit g x * resPushforward g W w :=
  rfl

/-- `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.ofPushforwardUnit` is the identity function,
so it is injective; this is the form in which the two laws of `pushforwardUnitScale` are checked
in the ring of sections rather than in the direct image. -/
public theorem ofPushforwardUnit_injective {W : T.Opensᵒᵖ}
    {a b : (pushforwardUnit g).val.obj W}
    (h : ofPushforwardUnit g a = ofPushforwardUnit g b) : a = b :=
  h

/-- **The powers of multiplication by a global unit, as a unital homomorphism of graded algebras
of `g_*𝒪_X` with itself**: in degree `n` it is multiplication by `wⁿ`.

This is the whole content of the rescaling invariance. The product law is `w^(i+j) = wⁱ · wʲ`
together with the commutativity of the structure sheaf, and the unit law is `w⁰ = 1`. `w` is
taken to be a unit because `pushforwardUnitGradedAlgebra` is nonzero in negative degrees too. -/
public def pushforwardUnitScale (w : Γ(X, ⊤)ˣ) :
    SheafOfModules.GradedAlgebra.UnitalHom (pushforwardUnitGradedAlgebra g)
      (pushforwardUnitGradedAlgebra g) where
  app n := pushforwardUnitMulBy g ((w ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤))
  map_mul i j W x y := by
    refine ofPushforwardUnit_injective g ?_
    change ofPushforwardUnit g x * ofPushforwardUnit g y *
        resPushforward g W ((w ^ (i + j) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) =
      ofPushforwardUnit g x * resPushforward g W ((w ^ i : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) *
        (ofPushforwardUnit g y * resPushforward g W ((w ^ j : Γ(X, ⊤)ˣ) : Γ(X, ⊤)))
    rw [zpow_add, Units.val_mul, map_mul, ringCatSheaf_mul_mul_mul_comm]
  map_one W := by
    refine ofPushforwardUnit_injective g ?_
    change ofPushforwardUnit g ((pushforwardUnitOne g).eval W) *
        resPushforward g W ((w ^ (0 : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) =
      ofPushforwardUnit g ((pushforwardUnitOne g).eval W)
    rw [zpow_zero, Units.val_one, map_one, mul_one]

@[simp]
public theorem pushforwardUnitScale_app (w : Γ(X, ⊤)ˣ) (n : ℤ) :
    (pushforwardUnitScale g w).app n =
      pushforwardUnitMulBy g ((w ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) :=
  rfl

/-! ### Every endomorphism of `𝒪_X` is multiplication by a global function -/

/-- **On sections, `unitMulBy` is multiplication by the restriction of `w`.** -/
@[simp]
public theorem ofUnit_unitMulBy_app (w : Γ(X, ⊤)) (V : X.Opensᵒᵖ)
    (x : (SheafOfModules.unit X.ringCatSheaf).val.obj V) :
    ofUnit X.ringCatSheaf ((unitMulBy w).val.app V x) =
      ofUnit X.ringCatSheaf x *
        (X.ringCatSheaf.obj.map (isTerminalTop.from V.unop).op).hom w :=
  rfl

/-- Restriction along the unique morphism `⊤ ⟶ ⊤` is the identity. -/
public theorem map_isTerminalTop_from_top (w : Γ(X, ⊤)) :
    (X.ringCatSheaf.obj.map (isTerminalTop.from (⊤ : X.Opens)).op).hom w = w := by
  rw [show (isTerminalTop.from (⊤ : X.Opens)).op = 𝟙 (op (⊤ : X.Opens)) from
    Subsingleton.elim _ _, X.ringCatSheaf.obj.map_id]
  rfl

/-- **The global function an endomorphism of `𝒪_X` multiplies by**: the image of the unit
section. -/
public def globalOfUnitEnd
    (α : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) : Γ(X, ⊤) :=
  ofUnit X.ringCatSheaf (α.val.app (op ⊤) (toUnit X.ringCatSheaf 1))

/-- **Every endomorphism of `𝒪_X` is multiplication by a global function**, namely by the image
of the unit section.

A morphism out of the unit sheaf of modules is determined by that image — Mathlib's
`SheafOfModules.unitHomEquiv` — and what this adds is that the compatible family of local
sections it corresponds to is the family of *restrictions of one global function*, because `⊤` is
terminal in the site of opens and the family is restriction-compatible. -/
public theorem eq_unitMulBy
    (α : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    α = unitMulBy (globalOfUnitEnd α) := by
  have h : Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop
        (globalOfUnitEnd α) =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv α := by
    ext V
    exact ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv α).property
      (isTerminalTop.from V.unop).op
  rw [unitMulBy, h, Equiv.symm_apply_apply]

@[simp]
public theorem globalOfUnitEnd_unitMulBy (w : Γ(X, ⊤)) :
    globalOfUnitEnd (unitMulBy w) = w := by
  show ofUnit X.ringCatSheaf (toUnit X.ringCatSheaf 1) *
      (X.ringCatSheaf.obj.map (isTerminalTop.from (⊤ : X.Opens)).op).hom w = w
  rw [map_isTerminalTop_from_top]
  exact one_mul w

/-- Multiplication by `1` is the identity: the identity multiplies by the image of the unit
section under itself. -/
@[simp]
public theorem unitMulBy_one : unitMulBy (1 : Γ(X, ⊤)) = 𝟙 _ :=
  (eq_unitMulBy (𝟙 (SheafOfModules.unit X.ringCatSheaf))).symm

/-- **The global function is multiplicative in the endomorphism.** -/
public theorem globalOfUnitEnd_comp
    (α β : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    globalOfUnitEnd (α ≫ β) = globalOfUnitEnd α * globalOfUnitEnd β :=
  (congrArg (fun γ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf =>
        ofUnit X.ringCatSheaf
          (γ.val.app (op ⊤) (α.val.app (op ⊤) (toUnit X.ringCatSheaf 1))))
      (eq_unitMulBy β)).trans
    ((ofUnit_unitMulBy_app (globalOfUnitEnd β) (op ⊤)
        (α.val.app (op ⊤) (toUnit X.ringCatSheaf 1))).trans
      (congrArg (globalOfUnitEnd α * ·) (map_isTerminalTop_from_top (globalOfUnitEnd β))))

/-- Multiplications by global functions compose to the multiplication by their product. -/
public theorem unitMulBy_comp (w w' : Γ(X, ⊤)) :
    unitMulBy w ≫ unitMulBy w' = unitMulBy (w * w') :=
  (eq_unitMulBy _).trans (congrArg unitMulBy
    ((globalOfUnitEnd_comp _ _).trans
      (congrArg₂ (· * ·) (globalOfUnitEnd_unitMulBy w) (globalOfUnitEnd_unitMulBy w'))))

/-- **The global function an automorphism of `𝒪_X` multiplies by, as a unit of `Γ(X, 𝒪)`**: its
inverse is the one the inverse automorphism multiplies by, because `globalOfUnitEnd` is
multiplicative and sends the identity to `1`. -/
public def unitOfUnitIso
    (α : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    Γ(X, ⊤)ˣ where
  val := globalOfUnitEnd α.hom
  inv := globalOfUnitEnd α.inv
  val_inv := (globalOfUnitEnd_comp α.hom α.inv).symm.trans (congrArg globalOfUnitEnd α.hom_inv_id)
  inv_val := (globalOfUnitEnd_comp α.inv α.hom).symm.trans (congrArg globalOfUnitEnd α.inv_hom_id)

@[simp]
public theorem unitOfUnitIso_val
    (α : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    ((unitOfUnitIso α : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = globalOfUnitEnd α.hom :=
  rfl

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

namespace Stacks.SymmetricDehomogenize

open Stacks.AlgebraicGeometry.ProjF1Dehomogenization

variable {X T : Scheme.{u}} (g : X ⟶ T) (F : T.Modules) (κ : F ⟶ pushforwardUnit g)

/-- **The graded map of a rescaled trivialization is the graded map followed by the scaling.**
Both sides are unital homomorphisms out of the symmetric algebra extending `w · κ` in degree one,
and `desc` is unique. There is no formula for the degree-`n` component of either side; the
equality is proved in every degree at once. -/
public theorem gradedHom_comp_pushforwardUnitMulBy (w : Γ(X, ⊤)ˣ) :
    gradedHom g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))) =
      (gradedHom g F κ).comp (pushforwardUnitScale g w) := by
  refine ((isSymmetricAlgebra_symmetricAlgebra T F).isUniversal.desc_unique
    (pushforwardUnitGradedAlgebra g) _
      (pairwiseCommutes_pushforwardUnit g F _) ?_).symm
  have h₁ : (pushforwardUnitScale g w).app 1 = pushforwardUnitMulBy g (w : Γ(X, ⊤)) :=
    congrArg (fun v : Γ(X, ⊤)ˣ => pushforwardUnitMulBy g (v : Γ(X, ⊤))) (zpow_one w)
  show symmetricAlgebraGen T F ≫ (gradedHom g F κ).app 1 ≫ (pushforwardUnitScale g w).app 1 =
    κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (pushforwardUnitScale g w).app 1) (gradedHom_degree_one g F κ))).trans
    (congrArg (κ ≫ ·) h₁)

/-- **The degree-`n` coefficient of the dehomogenization of a rescaled trivialization.** -/
public theorem datum_toFun_pushforwardUnitMulBy (U : T.Opens) {B : Type u} [CommRing B]
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) →+* B) (w : Γ(X, ⊤)ˣ) (n : ℕ)
    (x : ((Scheme.Modules.symmetricAlgebra T F).piece (n : ℤ)).val.obj (op U)) :
    (datum g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))) U φ).toFun (n : ℤ) x =
      φ (resPushforward g (op U) (w : Γ(X, ⊤))) ^ n *
        (datum g F κ U φ).toFun (n : ℤ) x := by
  have hg : ((gradedHom g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤)))).app
        (n : ℤ)).val.app (op U) x =
      (pushforwardUnitMulBy g ((w ^ (n : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤))).val.app (op U)
        (((gradedHom g F κ).app (n : ℤ)).val.app (op U) x) :=
    congrArg (fun h : SheafOfModules.GradedAlgebra.UnitalHom
        (Scheme.Modules.symmetricAlgebra T F) (pushforwardUnitGradedAlgebra g) =>
      (h.app (n : ℤ)).val.app (op U) x) (gradedHom_comp_pushforwardUnitMulBy g F κ w)
  have hw : ((w ^ (n : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = (w : Γ(X, ⊤)) ^ n :=
    (congrArg Units.val (zpow_natCast w n)).trans (Units.val_pow_eq_pow_val w n)
  have hu : resPushforward g (op U) ((w ^ (n : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) =
      resPushforward g (op U) (w : Γ(X, ⊤)) ^ n :=
    (congrArg (resPushforward g (op U)) hw).trans (map_pow _ _ _)
  have key : ofPushforwardUnit g
        ((pushforwardUnitMulBy g ((w ^ (n : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤))).val.app (op U)
          (((gradedHom g F κ).app (n : ℤ)).val.app (op U) x)) =
      ofPushforwardUnit g (((gradedHom g F κ).app (n : ℤ)).val.app (op U) x) *
        resPushforward g (op U) (w : Γ(X, ⊤)) ^ n :=
    (ofPushforwardUnit_pushforwardUnitMulBy_app g _ (op U) _).trans
      (congrArg (ofPushforwardUnit g (((gradedHom g F κ).app (n : ℤ)).val.app (op U) x) * ·) hu)
  refine ((congrArg (fun z => φ (ofPushforwardUnit g z)) hg).trans (congrArg φ key)).trans ?_
  exact ((map_mul φ _ _).trans
    (congrArg (φ (ofPushforwardUnit g (((gradedHom g F κ).app (n : ℤ)).val.app (op U) x)) * ·)
      (map_pow φ _ _))).trans (mul_comm _ _)

/-- **The dehomogenization of a rescaled trivialization is a graded unit multiple of the
original.** In degree `d` the two differ by `uᵈ`, with `u` the image of the rescaling unit. This
is exactly the hypothesis `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` consumes, and
the port to the symmetric algebra of
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize_pow_mul`. -/
public theorem dehomogenize_pow_mul (U : T.Opens) {B : Type u} [CommRing B]
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) →+* B) (hqc : IsQuasicoherentPieces F)
    (w : Γ(X, ⊤)ˣ) (n : ℕ) (a : (schemeSheafGradedAlgebra F hqc).sectionRing U)
    (ha : a ∈ (schemeSheafGradedAlgebra F hqc).grading U n) :
    dehomogenize g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))) U φ hqc a =
      φ (resPushforward g (op U) (w : Γ(X, ⊤))) ^ n *
        dehomogenize g F κ U φ hqc a := by
  obtain ⟨x, rfl⟩ := ha
  rw [dehomogenize_of, dehomogenize_of]
  exact datum_toFun_pushforwardUnitMulBy g F κ U φ w n x

/-- **The morphism to `Proj` of the graded ring of homogeneous sections does not depend on the
trivialization.** Rescaling `κ` by a global unit of `X` leaves
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the dehomogenization alone.

This is `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`, a step in the proof of
[Stacks, Tag 01NE], fed with `dehomogenize_pow_mul`. -/
public theorem fromOfGlobalSections_dehomogenize_congr_mulBy (U : T.Opens) {W : Scheme.{u}}
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) →+* Γ(W, ⊤)) (hqc : IsQuasicoherentPieces F)
    (w : Γ(X, ⊤)ˣ)
    (h : (HomogeneousIdeal.irrelevant
        ((schemeSheafGradedAlgebra F hqc).grading U)).toIdeal.map
      (dehomogenize g F κ U φ hqc) = ⊤)
    (h' : (HomogeneousIdeal.irrelevant
        ((schemeSheafGradedAlgebra F hqc).grading U)).toIdeal.map
      (dehomogenize g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))) U φ hqc) = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections ((schemeSheafGradedAlgebra F hqc).grading U)
        (dehomogenize g F κ U φ hqc) h =
      AlgebraicGeometry.Proj.fromOfGlobalSections ((schemeSheafGradedAlgebra F hqc).grading U)
        (dehomogenize g F (κ ≫ pushforwardUnitMulBy g (w : Γ(X, ⊤))) U φ hqc) h' := by
  have hinv : ∀ v : Γ(X, ⊤)ˣ, φ (resPushforward g (op U) (v : Γ(X, ⊤))) *
      φ (resPushforward g (op U) ((v⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))) = 1 := by
    intro v
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  exact AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit _ _ _
    ⟨φ (resPushforward g (op U) (w : Γ(X, ⊤))),
      φ (resPushforward g (op U) ((w⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))), hinv w,
      (mul_comm _ _).trans (hinv w)⟩
    (fun d a ha => dehomogenize_pow_mul g F κ U φ hqc w d a ha) h h'

end Stacks.SymmetricDehomogenize

end
