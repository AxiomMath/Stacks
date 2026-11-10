module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedBaseChange

/-!
# The functor out of `Crystalline.Pair`: the assignment `T ↦ M ⊗_{D,f} B`

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] runs in the direction opposite to the
functor of [Stacks, Lemma 60.17.3, Tag 07JG]: given a pair `(M, ∇)` satisfying the four items
(07JB), (07JC), (07JD) and (07JE), it constructs a crystal in quasi-coherent
`𝒪_{X/S}`-modules by sending an affine object `(U, T, δ)` of `Cris(X/S)`, with `T = Spec(B)`, to

`ℱ_T = M ⊗_{D,f} B`

for a divided power map `f : D → B` in `Cris(X/S)`, which [Stacks, Lemma 60.5.6, Tag 07HP]
supplies.  Two choices of `f` are compared by the Taylor isomorphism `c_{f,g}`, and the cocycle
identity `c_{g,h} ∘ c_{f,g} = c_{f,h}` makes the module independent of the choice.

This module builds that assignment as a functor out of `Crystalline.Pair`, over the site on
which the choice of `f` is part of the datum.

## The pointed site

The category on which the assignment is functorial is the coslice `Under Dt` of the affine
crystalline site `CRIS(C/A)` under the fixed object `Dt`: an object is a divided power thickening
`(B, J_B, δ)` of `C` over `A` together with a morphism `f : Dt ⟶ B` of thickenings, and a
morphism is a morphism `u : B ⟶ B'` of thickenings with `u ∘ f = f'`.  On that site the
assignment is a base change along a varying ring map, so the tensor product is the twisted one
`Crystalline.TwistedScalars`: `M ⊗_{D,f} B = TwistedScalars f ⊗_D M`.  The functor takes its
values in `ModuleCat D`; the `B`-module structure of each value is respected by the restriction
maps and by the image of a horizontal map of pairs.

## Main definitions

* `Crystalline.PointedThickening` — the pointed affine crystalline site `Under Dt`, and
  `Crystalline.pointRingHom` the chosen divided power map `f : D → B` of an object.
* `Crystalline.pointedSections` — **the module `M ⊗_{D,f} B` of the source's construction.**
* `Crystalline.pointedScalarsMap`, `Crystalline.pointedRestriction` — **the restriction maps**,
  `u ⊗ id : M ⊗_{D,f} B → M ⊗_{D,f'} B'` along a morphism of pointed objects.
* `Crystalline.pairCrystal` — **the crystal of a pair**: the functor
  `Under Dt ⥤ ModuleCat D` carrying the object assignment and the restriction maps.
* `Crystalline.pairToCrystal` — **the functor out of `Crystalline.Pair`**, sending a pair to its
  crystal and a horizontal map to the family `id ⊗ φ` of restriction-compatible maps.
* `Crystalline.secondDividedPowerMapOfPointings` — the datum `f`, `g` of the Taylor comparison,
  assembled from two pointings of one object.
* `Crystalline.pointedComparison` — **the comparison `c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`** of
  two pointings of one object of the site, and `Crystalline.pointedUnitComparison` its
  degree-zero case `m ↦ 1 ⊗ m`.
* `Crystalline.selfPoint` — the tautological object `(D, id)` of the pointed site, and
  `Crystalline.pointedSectionsSelfEquiv` the identification `M ⊗_{D,id} D ≅ M`.

## Main results

* `Crystalline.pointedRestriction_smul` — the restriction map is **semilinear** over the
  underlying map of rings: `u ⊗ id` is `u`-semilinear.
* `Crystalline.pairToCrystal_map_app_smul` — the maps of the image of a horizontal map of pairs
  are `B`-**linear** at every object.
* `Crystalline.sub_pointRingHom_mem_ideal` — **two pointings of one object agree modulo the
  divided power ideal of `B`.**  This is the source's "since `f` and `g` are morphisms in
  `Cris(X/S)` we see that the image of `f - g : D → B` is contained in the divided power ideal
  `J_B`", under the hypothesis that `C → D/J_D` is surjective.
* `Crystalline.pairToCrystal_faithful` — **the functor out of `Crystalline.Pair` is faithful**.
* `Crystalline.pointedComparison_self` — **`c_{f,f} = 1`**, and
  `Crystalline.pointedComparison_comp` — **the cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}` as an
  identity of maps**.
* `Crystalline.pairCrystalSelfPointIso` — the crystal of a pair, evaluated at the tautological
  object, is the pair's own module.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w uI

namespace Crystalline

/-! ### The pointed affine crystalline site -/

section Pointed

variable {S : AffineCrystallineSituation.{u, v}}

variable (Dt : DividedPowerThickening.{u, v, w} S) in
/-- **The pointed affine crystalline site.**  An object is a divided power thickening of `C` over
`A` together with a morphism `f : Dt ⟶ B` of thickenings; a morphism is a morphism of
thickenings commuting with the two chosen maps. -/
abbrev PointedThickening := Under Dt

variable {Dt : DividedPowerThickening.{u, v, w} S}

/-- **The chosen divided power map `f : D → B`** of an object of the pointed site, as a ring
homomorphism. -/
def pointRingHom (T : PointedThickening Dt) :
    Dt.ring.carrier →+* T.right.ring.carrier :=
  T.hom.hom.toRingHom

/-- The underlying ring homomorphism of a morphism of pointed objects. -/
def pointedHomRingHom {T T' : PointedThickening Dt} (u : T ⟶ T') :
    T.right.ring.carrier →+* T'.right.ring.carrier :=
  u.right.hom.toRingHom

/-- **The triangle of the pointed site, at the level of ring homomorphisms**: a morphism of
pointed objects carries the chosen map of its source to the chosen map of its target. -/
@[simp] theorem pointedHomRingHom_pointRingHom {T T' : PointedThickening Dt} (u : T ⟶ T')
    (a : Dt.ring.carrier) :
    pointedHomRingHom u (pointRingHom T a) = pointRingHom T' a :=
  congrArg (fun phi : Dt ⟶ T'.right ↦ phi.hom a) (Under.w u)

/-- The ring homomorphism underlying the identity is the identity. -/
@[simp] theorem pointedHomRingHom_id (T : PointedThickening Dt) (b : T.right.ring.carrier) :
    pointedHomRingHom (𝟙 T) b = b := rfl

/-- The ring homomorphism underlying a composite is the composite. -/
@[simp] theorem pointedHomRingHom_comp {T T' T'' : PointedThickening Dt} (u : T ⟶ T')
    (v : T' ⟶ T'') (b : T.right.ring.carrier) :
    pointedHomRingHom (u ≫ v) b = pointedHomRingHom v (pointedHomRingHom u b) := rfl

end Pointed

/-! ### The module `M ⊗_{D,f} B` and the restriction maps -/

section Sections

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M]

/-- **The module `M ⊗_{D,f} B` of the proof of [Stacks, Proposition 60.17.4, Tag 07JH]**: the
base change of `M` along the chosen divided power map of a pointed object, taken over the twisted
`D`-algebra structure `Crystalline.TwistedScalars` that map induces on `B`. -/
abbrev pointedSections (T : PointedThickening Dt) : Type w :=
  TwistedScalars (pointRingHom T) ⊗[Dt.ring.carrier] M

variable {M}

/-- **The restriction map on scalars** along a morphism of pointed objects: the underlying ring
map `u : B → B'`, read as a `D`-linear map of the two twisted algebras. -/
def pointedScalarsMap {T T' : PointedThickening Dt} (u : T ⟶ T') :
    TwistedScalars (pointRingHom T) →ₗ[Dt.ring.carrier] TwistedScalars (pointRingHom T') where
  toFun b := TwistedScalars.mk _ (pointedHomRingHom u b.val)
  map_add' b b' := by
    change pointedHomRingHom u (TwistedScalars.val b + TwistedScalars.val b') =
      pointedHomRingHom u b.val + pointedHomRingHom u b'.val
    exact map_add _ _ _
  map_smul' a b := by
    change pointedHomRingHom u (TwistedScalars.val (a • b)) =
      pointRingHom T' a * pointedHomRingHom u b.val
    rw [TwistedScalars.smul_val, map_mul, pointedHomRingHom_pointRingHom]

/-- The map on scalars is the underlying ring homomorphism. -/
@[simp] theorem pointedScalarsMap_val {T T' : PointedThickening Dt} (u : T ⟶ T')
    (b : TwistedScalars (pointRingHom T)) :
    (pointedScalarsMap u b).val = pointedHomRingHom u b.val := rfl

/-- The map on scalars carries a `b`-multiple to the `u(b)`-multiple. -/
theorem pointedScalarsMap_smul {T T' : PointedThickening Dt} (u : T ⟶ T')
    (b : T.right.ring.carrier) (c : TwistedScalars (pointRingHom T)) :
    pointedScalarsMap u (b • c) = pointedHomRingHom u b • pointedScalarsMap u c := by
  change pointedHomRingHom u (TwistedScalars.val (b • c)) =
    pointedHomRingHom u b * pointedHomRingHom u c.val
  rw [TwistedScalars.val_smul, map_mul]

variable (M)

/-- **The restriction map `M ⊗_{D,f} B → M ⊗_{D,f'} B'`** along a morphism `u` of pointed
objects, that is `u ⊗ id`. -/
noncomputable def pointedRestriction {T T' : PointedThickening Dt} (u : T ⟶ T') :
    pointedSections M T →ₗ[Dt.ring.carrier] pointedSections M T' :=
  LinearMap.rTensor M (pointedScalarsMap u)

/-- The restriction map on a pure tensor `b ⊗ m` is `u(b) ⊗ m`. -/
@[simp] theorem pointedRestriction_tmul {T T' : PointedThickening Dt} (u : T ⟶ T')
    (b : TwistedScalars (pointRingHom T)) (m : M) :
    pointedRestriction M u (b ⊗ₜ[Dt.ring.carrier] m) =
      pointedScalarsMap u b ⊗ₜ[Dt.ring.carrier] m := rfl

/-- The restriction map along the identity is the identity. -/
@[simp] theorem pointedRestriction_id (T : PointedThickening Dt) :
    pointedRestriction M (𝟙 T) = LinearMap.id := by
  refine TensorProduct.ext' fun b m ↦ ?_
  rw [pointedRestriction_tmul]
  rfl

/-- The restriction maps compose. -/
theorem pointedRestriction_comp {T T' T'' : PointedThickening Dt} (u : T ⟶ T')
    (v : T' ⟶ T'') : pointedRestriction M (u ≫ v) =
      (pointedRestriction M v).comp (pointedRestriction M u) := by
  refine TensorProduct.ext' fun b m ↦ ?_
  rw [pointedRestriction_tmul, LinearMap.comp_apply, pointedRestriction_tmul,
    pointedRestriction_tmul]
  rfl

/-- **The restriction map is semilinear over the underlying map of rings**: `u ⊗ id` sends a
`b`-multiple to the `u(b)`-multiple. -/
theorem pointedRestriction_smul {T T' : PointedThickening Dt} (u : T ⟶ T')
    (b : T.right.ring.carrier) (z : pointedSections M T) :
    pointedRestriction M u (b • z) =
      pointedHomRingHom u b • pointedRestriction M u z := by
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
      rw [TensorProduct.smul_tmul', pointedRestriction_tmul, pointedRestriction_tmul,
        TensorProduct.smul_tmul', pointedScalarsMap_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end Sections

/-! ### The crystal of a pair, and the functor out of `Crystalline.Pair` -/

section Functor

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  (p : ℕ) (Omega : Type v) [AddCommGroup Omega] [Module Dt.ring.carrier Omega]
  {ι : Type uI} (dx : ι → Omega) (d : Dt.ring.carrier → Omega)

/-- **The crystal of a pair `(M, ∇)`**: the assignment `T ↦ M ⊗_{D,f} B` of the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] on the pointed affine crystalline site, with the
restriction maps `u ⊗ id`. -/
noncomputable def pairCrystal
    (P : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d) :
    PointedThickening Dt ⥤ ModuleCat.{w} Dt.ring.carrier where
  obj T := ModuleCat.of _ (pointedSections P.carrier T)
  map u := ModuleCat.ofHom (pointedRestriction P.carrier u)
  map_id T := by rw [pointedRestriction_id]; rfl
  map_comp u v := by rw [pointedRestriction_comp]; rfl

/-- The value of the crystal of a pair at a pointed object `T` is `M ⊗_{D,f} B`. -/
@[simp] theorem pairCrystal_obj
    (P : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d) (T : PointedThickening Dt) :
    (pairCrystal p Omega dx d P).obj T = ModuleCat.of _ (pointedSections P.carrier T) := rfl

/-- The crystal of a pair sends a morphism of pointed objects to its restriction map. -/
@[simp] theorem pairCrystal_map
    (P : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d)
    {T T' : PointedThickening Dt} (u : T ⟶ T') :
    (pairCrystal p Omega dx d P).map u = ModuleCat.ofHom (pointedRestriction P.carrier u) := rfl

/-- **The functor out of `Crystalline.Pair`.**  A pair goes to its crystal
`T ↦ M ⊗_{D,f} B`, and a horizontal map `φ : M → N` of pairs to the family `id ⊗ φ`, which
commutes with the restriction maps. -/
noncomputable def pairToCrystal :
    Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d ⥤
      (PointedThickening Dt ⥤ ModuleCat.{w} Dt.ring.carrier) where
  obj P := pairCrystal p Omega dx d P
  map {_ _} phi :=
    { app := fun T ↦ ModuleCat.ofHom
        (LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi.toLinearMap)
      naturality := fun _ _ _ ↦
        ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl) }
  map_id _ := NatTrans.ext (funext fun _ ↦
    ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl))
  map_comp _ _ := NatTrans.ext (funext fun _ ↦
    ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl))

/-- The functor out of `Crystalline.Pair` sends a pair to its crystal. -/
@[simp] theorem pairToCrystal_obj
    (P : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d) :
    (pairToCrystal p Omega dx d).obj P = pairCrystal p Omega dx d P := rfl

/-- The image of a horizontal map `φ` of pairs is `id ⊗ φ` at every pointed object. -/
@[simp] theorem pairToCrystal_map_app
    {P Q : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d} (phi : P ⟶ Q)
    (T : PointedThickening Dt) :
    ((pairToCrystal p Omega dx d).map phi).app T =
      ModuleCat.ofHom
        (LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi.toLinearMap) := rfl

/-- **The image of a horizontal map of pairs is `B`-linear at every object.** -/
theorem pairToCrystal_map_app_smul
    {P Q : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d} (phi : P ⟶ Q)
    (T : PointedThickening Dt) (b : T.right.ring.carrier)
    (z : pointedSections P.carrier T) :
    LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi.toLinearMap (b • z) =
      b • LinearMap.lTensor (TwistedScalars (pointRingHom T)) phi.toLinearMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul c m => rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end Functor

/-! ### The tautological object `(D, id)`, and faithfulness -/

section Self

variable {S : AffineCrystallineSituation.{u, v}} (Dt : DividedPowerThickening.{u, v, w} S)

/-- **The tautological object of the pointed site**: the thickening `Dt` itself, pointed by its
identity. -/
abbrev selfPoint : PointedThickening Dt :=
  { left := ⟨⟨⟩⟩, right := Dt, hom := 𝟙 Dt }

/-- The chosen map of the tautological object is the identity. -/
@[simp] theorem pointRingHom_selfPoint (a : Dt.ring.carrier) :
    pointRingHom (selfPoint Dt) a = a := rfl

variable {Dt} (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M]

/-- **The retraction `M ⊗_{D,id} D → M`** of the tautological object, that is `b ⊗ m ↦ b · m`:
the semilinear base change `Crystalline.semilinearBaseChange` of the identity of `M`. -/
noncomputable def pointedSectionsSelfRetraction :
    pointedSections M (selfPoint Dt) →ₗ[Dt.ring.carrier] M :=
  semilinearBaseChange (LinearMap.id : M →ₗ[Dt.ring.carrier] M)

/-- The retraction sends `1 ⊗ m` to `m`. -/
@[simp] theorem pointedSectionsSelfRetraction_one_tmul (m : M) :
    pointedSectionsSelfRetraction M
      ((1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier] m) = m :=
  semilinearBaseChange_one_tmul (LinearMap.id : M →ₗ[Dt.ring.carrier] M) m

/-- The retraction sends `b ⊗ m` to `b · m`. -/
@[simp] theorem pointedSectionsSelfRetraction_tmul
    (b : TwistedScalars (pointRingHom (selfPoint Dt))) (m : M) :
    pointedSectionsSelfRetraction M (b ⊗ₜ[Dt.ring.carrier] m) = TwistedScalars.val b • m :=
  semilinearBaseChange_tmul (LinearMap.id : M →ₗ[Dt.ring.carrier] M) b m

/-- **The identification `M ⊗_{D,id} D ≅ M`**: the retraction `b ⊗ m ↦ b · m` is a `D`-linear
isomorphism with inverse `m ↦ 1 ⊗ m`. -/
noncomputable def pointedSectionsSelfEquiv :
    pointedSections M (selfPoint Dt) ≃ₗ[Dt.ring.carrier] M :=
  LinearEquiv.ofLinearMap (pointedSectionsSelfRetraction M)
    (TensorProduct.mk Dt.ring.carrier (TwistedScalars (pointRingHom (selfPoint Dt))) M 1 :
      M →ₗ[Dt.ring.carrier] pointedSections M (selfPoint Dt))
    (LinearMap.ext fun m ↦ pointedSectionsSelfRetraction_one_tmul M m)
    (TensorProduct.ext' fun b m ↦ by
      change (1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier]
          (TwistedScalars.val b • m) = b ⊗ₜ[Dt.ring.carrier] m
      rw [← TensorProduct.smul_tmul]
      congr 1
      have hval := TwistedScalars.smul_val (f := pointRingHom (selfPoint Dt))
        (TwistedScalars.val b) 1
      rw [pointRingHom_selfPoint, TwistedScalars.val_one, mul_one] at hval
      exact hval)

/-- The identification `M ⊗_{D,id} D ≅ M` sends `1 ⊗ m` to `m`. -/
@[simp] theorem pointedSectionsSelfEquiv_one_tmul (m : M) :
    pointedSectionsSelfEquiv M
      ((1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier] m) = m :=
  pointedSectionsSelfRetraction_one_tmul M m

variable {M} (p : ℕ) (Omega : Type v) [AddCommGroup Omega] [Module Dt.ring.carrier Omega]
  {ι : Type uI} (dx : ι → Omega) (d : Dt.ring.carrier → Omega)

/-- **The crystal of a pair, at the tautological object, is the pair's own module.** -/
noncomputable def pairCrystalSelfPointIso
    (P : Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d) :
    (pairCrystal p Omega dx d P).obj (selfPoint Dt) ≅
      ModuleCat.of Dt.ring.carrier P.carrier :=
  (pointedSectionsSelfEquiv P.carrier).toModuleIso

/-- **The functor out of `Crystalline.Pair` is faithful.** -/
theorem pairToCrystal_faithful :
    Functor.Faithful
      (pairToCrystal p Omega dx d :
        Pair.{w, v, uI, w} p Dt.ring.carrier Omega dx d ⥤
          (PointedThickening Dt ⥤ ModuleCat.{w} Dt.ring.carrier)) where
  map_injective {P Q} phi psi h := by
    refine PairHom.ext (LinearMap.ext fun m ↦ ?_)
    have happ : LinearMap.lTensor (TwistedScalars (pointRingHom (selfPoint Dt)))
          phi.toLinearMap
          ((1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier] m) =
        LinearMap.lTensor (TwistedScalars (pointRingHom (selfPoint Dt))) psi.toLinearMap
          ((1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier] m) :=
      congrArg
        (fun eta : pairCrystal p Omega dx d P ⟶ pairCrystal p Omega dx d Q ↦
          (eta.app (selfPoint Dt)).hom
            ((1 : TwistedScalars (pointRingHom (selfPoint Dt))) ⊗ₜ[Dt.ring.carrier] m)) h
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul] at happ
    exact (pointedSectionsSelfRetraction_one_tmul Q.carrier _).symm.trans
      ((congrArg (pointedSectionsSelfRetraction Q.carrier) happ).trans
        (pointedSectionsSelfRetraction_one_tmul Q.carrier _))

end Self

/-! ### The comparison of two pointings of one object -/

section Comparison

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M]
  {X : DividedPowerThickening.{u, v, w} S}

/-- A morphism `f : Dt ⟶ X` of thickenings, read as an object of the pointed site: the object `X`
pointed by `f`. -/
abbrev pointedOfHom (f : Dt ⟶ X) : PointedThickening Dt :=
  { left := ⟨⟨⟩⟩, right := X, hom := f }

/-- The chosen map of the object pointed by `f` is `f`. -/
@[simp] theorem pointRingHom_pointedOfHom (f : Dt ⟶ X) (a : Dt.ring.carrier) :
    pointRingHom (pointedOfHom f) a = f.hom a := rfl

/-- **The comparison `c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B` of the proof of
[Stacks, Proposition 60.17.4, Tag 07JH]**, for two pointings of one object of the pointed
crystalline site: the `B`-linear extension, by `Crystalline.semilinearBaseChange`, of a semilinear
map `M →ₛₗ[f] M ⊗_{D,g} B`. -/
noncomputable def pointedComparison (f g : Dt ⟶ X)
    (Tmap : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g)) :
    pointedSections M (pointedOfHom f) →ₗ[X.ring.carrier] pointedSections M (pointedOfHom g) :=
  semilinearBaseChange Tmap

/-- The comparison of a semilinear map `T` sends `1 ⊗ m` to `T m`. -/
@[simp] theorem pointedComparison_one_tmul (f g : Dt ⟶ X)
    (Tmap : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g)) (m : M) :
    pointedComparison M f g Tmap
        ((1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m) = Tmap m :=
  semilinearBaseChange_one_tmul Tmap m

/-- **The degree-zero comparison `m ↦ 1 ⊗ m`**, as a semilinear map for the pointing `f`. -/
noncomputable def pointedUnitComparison (f : Dt ⟶ X) :
    M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom f) where
  toFun m := (1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m
  map_add' m m' := TensorProduct.tmul_add _ m m'
  map_smul' a m := by
    change (1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] (a • m) =
      pointRingHom (pointedOfHom f) a •
        ((1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    have hscalar : a • (1 : TwistedScalars (pointRingHom (pointedOfHom f))) =
        pointRingHom (pointedOfHom f) a •
          (1 : TwistedScalars (pointRingHom (pointedOfHom f))) :=
      (TwistedScalars.smul_val (f := pointRingHom (pointedOfHom f)) a 1).trans
        (TwistedScalars.val_smul (f := pointRingHom (pointedOfHom f))
          (pointRingHom (pointedOfHom f) a) 1).symm
    exact congrArg (fun b ↦ b ⊗ₜ[Dt.ring.carrier] m) hscalar

/-- The degree-zero comparison sends `m` to `1 ⊗ m`. -/
@[simp] theorem pointedUnitComparison_apply (f : Dt ⟶ X) (m : M) :
    pointedUnitComparison M f m =
      (1 : TwistedScalars (pointRingHom (pointedOfHom f))) ⊗ₜ[Dt.ring.carrier] m := rfl

/-- **`c_{f,f} = 1`**: the comparison of the degree-zero map `m ↦ 1 ⊗ m` at one pointing is the
identity. -/
theorem pointedComparison_self (f : Dt ⟶ X) :
    pointedComparison M f f (pointedUnitComparison M f) = LinearMap.id := by
  refine (semilinearBaseChange_unique (pointedUnitComparison M f) LinearMap.id ?_).symm
  intro m
  rw [LinearMap.id_apply, pointedUnitComparison_apply]

/-- **The cocycle `c_{g,h} ∘ c_{f,g} = c_{f,h}` as an identity of maps**, the source's "A
computation shows that `c_{g,h} ∘ c_{f,g} = c_{f,h}`": the composite of the comparisons of two
pointings is again a comparison, namely the one of the single semilinear map
`c_{g,h} ∘ T_{f,g}`. -/
theorem pointedComparison_comp (f g h : Dt ⟶ X)
    (T₁ : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (T₂ : M →ₛₗ[pointRingHom (pointedOfHom g)] pointedSections M (pointedOfHom h)) :
    (pointedComparison M g h T₂).comp (pointedComparison M f g T₁) =
      pointedComparison M f h ((pointedComparison M g h T₂).comp T₁) :=
  (semilinearBaseChange_comp T₁ (semilinearBaseChange T₂)).symm

end Comparison

/-! ### Two pointings of one object: the datum of the Taylor comparison -/

section TwoPointings

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}

/-- **Two pointings of one object agree modulo the divided power ideal of `B`.**  This is the
source's "since `f` and `g` are morphisms in `Cris(X/S)` we see that the image of `f - g : D → B`
is contained in the divided power ideal `J_B`", and it is what makes the differences
`ξ_i = f(x_i) - g(x_i)` of the Taylor series lie in an ideal with divided powers.  The hypothesis
is surjectivity of the structural map `C → D/J_D` of the fixed object. -/
theorem sub_pointRingHom_mem_ideal (hDt : Function.Surjective Dt.toQuotient)
    {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X) (a : Dt.ring.carrier) :
    f.hom a - g.hom a ∈ X.ring.ideal := by
  obtain ⟨c, hc⟩ := hDt (Ideal.Quotient.mk Dt.ring.ideal a)
  have key : ∀ h : Dt ⟶ X,
      Ideal.Quotient.mk X.ring.ideal (h.hom a) = X.toQuotient c := by
    intro h
    have hcomp := congrArg (fun phi ↦ phi c) h.toQuotient_comp
    simp only [RingHom.coe_comp, Function.comp_apply] at hcomp
    rw [hc] at hcomp
    rw [← hcomp]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key f, key g, sub_self]

/-- **The datum of the Taylor comparison, assembled from two pointings of one object.**  Given
two morphisms `f, g : Dt ⟶ X` of thickenings and a `D`-algebra structure on `B` whose structure
map is `g`, the pair `(f, g)` is a `Crystalline.SecondDividedPowerMap`. -/
def secondDividedPowerMapOfPointings (hDt : Function.Surjective Dt.toQuotient)
    {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X)
    [Algebra Dt.ring.carrier X.ring.carrier]
    (hg : ∀ a : Dt.ring.carrier,
      algebraMap Dt.ring.carrier X.ring.carrier a = g.hom a) :
    SecondDividedPowerMap Dt.ring X.ring where
  hom := f.hom
  sub_algebraMap_mem a := by
    rw [hg a]
    exact sub_pointRingHom_mem_ideal hDt f g a

/-- The ring homomorphism of the datum assembled from two pointings `f, g` is `f`. -/
@[simp] theorem secondDividedPowerMapOfPointings_ringHom
    (hDt : Function.Surjective Dt.toQuotient)
    {X : DividedPowerThickening.{u, v, w} S} (f g : Dt ⟶ X)
    [Algebra Dt.ring.carrier X.ring.carrier]
    (hg : ∀ a : Dt.ring.carrier,
      algebraMap Dt.ring.carrier X.ring.carrier a = g.hom a)
    (a : Dt.ring.carrier) :
    (secondDividedPowerMapOfPointings hDt f g hg).ringHom a = f.hom a := rfl

end TwoPointings

end Crystalline

end
