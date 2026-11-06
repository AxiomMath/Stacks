module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# Inverse image of ℓ-adic sheaves with coefficients

The inverse image `f⁻¹` of ℓ-adic sheaves is additive: at each level it is the inverse image of
sheaves of `ℤ/ℓ^{n+1}`-modules, a left adjoint between preadditive categories with biproducts,
which preserves binary coproducts and hence binary biproducts. So an action `O → End F` of a
finite `ℤ_ℓ`-algebra on an ℓ-adic sheaf (`LAdicSheaf.CoefficientSheaf`, Weil II 1.1.1) induces an
action on `f⁻¹F`: the inverse image of `O`-sheaves.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageEndRingHom`: `End F → End f⁻¹F`.
* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.inverseImage`: `f⁻¹` on `O`-sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

namespace LAdicSheaf

/-- The inverse image at each level is additive, being a left adjoint. -/
public instance additive_levelPullback (n : ℕ) : (levelPullback (ℓ := ℓ) f n).Additive :=
  (levelAdjunction f n).left_adjoint_additive

variable [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The inverse image of ℓ-adic sheaves is additive.** -/
public instance additive_inverseImageFunctor :
    (inverseImageFunctor (ℓ := ℓ) f).Additive where
  map_add {_ _} {a b} := LAdicSheaf.Hom.ext (h := fun n =>
    (levelPullback (ℓ := ℓ) f n).map_add (f := a.app n) (g := b.app n))

/-- The ring homomorphism `End F → End f⁻¹F`. -/
public def inverseImageEndRingHom (F : LAdicSheaf.{u, u + 1} B Y ℓ) :
    End F →+* End (inverseImage f F) where
  toFun a := .of ((inverseImageFunctor f).map a.asHom)
  map_one' := End.ext ((inverseImageFunctor f).map_id F)
  map_mul' a b := End.ext ((inverseImageFunctor f).map_comp b.asHom a.asHom)
  map_zero' := End.ext ((inverseImageFunctor f).map_zero F F)
  map_add' a b := End.ext ((inverseImageFunctor f).map_add (f := a.asHom) (g := b.asHom))

end LAdicSheaf

end AlgebraicGeometry.SmallEtale

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]

/-- **The inverse image of an ℓ-adic sheaf with coefficients in `O`**: the inverse image of the
underlying ℓ-adic sheaf, with the inverse image of the action. -/
public def inverseImage (F : LAdicSheaf.CoefficientSheaf B Y ℓ O) :
    LAdicSheaf.CoefficientSheaf B X ℓ O where
  toLAdicSheaf := AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F.toLAdicSheaf
  act :=
    (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageEndRingHom f F.toLAdicSheaf).comp F.act

/-- An element `o : O` acts on `f⁻¹F` by the inverse image of its action on `F`. -/
public theorem inverseImage_act (F : LAdicSheaf.CoefficientSheaf B Y ℓ O) (o : O) :
    ((inverseImage f F).act o).asHom =
      AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f (F.act o).asHom :=
  rfl

end Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf
