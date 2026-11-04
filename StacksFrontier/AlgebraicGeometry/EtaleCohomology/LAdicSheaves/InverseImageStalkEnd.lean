module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.GeometricPointStalkMapNaturality

/-!
# The stalks of an inverse image intertwine the endomorphisms of the geometric point

Let `f : X ⟶ Y` be a morphism of Noetherian schemes, `F` an ℓ-adic sheaf on `Y`, `x̄` a geometric
point of `X` and `a` an endomorphism of `x̄`, which is also an endomorphism of `f(x̄)`. The
identification `(f⁻¹F)_x̄ ≅ F_{f(x̄)}` of ℓ-adic stalks
(`Stacks.EtaleCohomology.inverseImageStalkEquiv`) carries the action of `a` on the left to its
action on the right: at each finite level this is the naturality of the stalk of an inverse image
in the geometric point
(`AlgebraicGeometry.geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom`). In
particular the geometric Frobenius at a closed point acts on `(f⁻¹F)_x̄` as on `F_{f(x̄)}`, with
the same trace, on the ℓ-adic and on the rational stalks.

## Main results

* `Stacks.EtaleCohomology.finiteLevelStalkEnd_inverseImageFiniteLevelStalkIso_hom`: the level-`n`
  compatibility.
* `Stacks.EtaleCohomology.inverseImageStalkEquiv_stalkEnd`: the ℓ-adic compatibility.
* `Stacks.EtaleCohomology.rationalInverseImageStalkEquiv`: the rational stalks.
* `Stacks.EtaleCohomology.rationalInverseImageStalkEquiv_rationalStalkEnd` and
  `Stacks.EtaleCohomology.trace_inverseImage_rationalStalkEnd`: the rational compatibility, and
  equality of traces.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
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
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The level-`n` stalks of `f⁻¹F` and of `F` intertwine the actions of an endomorphism of the
geometric point.** -/
public theorem finiteLevelStalkEnd_inverseImageFiniteLevelStalkIso_hom (F : LAdicSheaf B Y ℓ)
    (x : GeometricPoint X.obj) (a : GeometricPoint.Hom x x) (n : ℕ) :
    finiteLevelStalkEnd B X ℓ (LAdicSheaf.inverseImage f F) a n ≫
        (inverseImageFiniteLevelStalkIso B f F x n).hom =
      (inverseImageFiniteLevelStalkIso B f F x n).hom ≫
        finiteLevelStalkEnd B Y ℓ F (a.mapHom (B.inclusion.map f)) n :=
  let : HasProducts.{u} (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun _ => ModuleCat.hasLimitsOfShape
  geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom B f x _ a (F.level n)

/-- **The ℓ-adic stalks of `f⁻¹F` and of `F` intertwine the actions of an endomorphism of the
geometric point.** -/
public theorem inverseImageStalkEquiv_stalkEnd (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj)
    (a : GeometricPoint.Hom x x) (v : LAdicSheaf.stalk B X ℓ (LAdicSheaf.inverseImage f F) x) :
    inverseImageStalkEquiv B f F x (LAdicSheaf.stalkEnd B X ℓ (LAdicSheaf.inverseImage f F) a v) =
      LAdicSheaf.stalkEnd B Y ℓ F (a.mapHom (B.inclusion.map f))
        (inverseImageStalkEquiv B f F x v) :=
  Subtype.ext (funext fun n => ConcreteCategory.congr_hom
    (finiteLevelStalkEnd_inverseImageFiniteLevelStalkIso_hom B f F x a n) (v.1 n))

/-- The same, as an identity of `ℤ_ℓ`-linear maps. -/
public theorem inverseImageStalkEquiv_comp_stalkEnd (F : LAdicSheaf B Y ℓ)
    (x : GeometricPoint X.obj) (a : GeometricPoint.Hom x x) :
    (inverseImageStalkEquiv B f F x).toLinearMap ∘ₗ
        LAdicSheaf.stalkEnd B X ℓ (LAdicSheaf.inverseImage f F) a =
      LAdicSheaf.stalkEnd B Y ℓ F (a.mapHom (B.inclusion.map f)) ∘ₗ
        (inverseImageStalkEquiv B f F x).toLinearMap :=
  LinearMap.ext (inverseImageStalkEquiv_stalkEnd B f F x a)

/-- The rational stalks of `f⁻¹F` at `x̄` and of `F` at `f(x̄)`. -/
public def rationalInverseImageStalkEquiv (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj) :
    LAdicSheaf.rationalStalkLeft B X ℓ (LAdicSheaf.inverseImage f F) x ≃ₗ[Padic ℓ]
      LAdicSheaf.rationalStalkLeft B Y ℓ F (x.map (B.inclusion.map f)) :=
  (inverseImageStalkEquiv B f F x).baseChange (PadicInt ℓ) (Padic ℓ) _ _

/-- **The rational stalks of `f⁻¹F` and of `F` intertwine the actions of an endomorphism of the
geometric point.** -/
public theorem rationalInverseImageStalkEquiv_rationalStalkEnd (F : LAdicSheaf B Y ℓ)
    (x : GeometricPoint X.obj) (a : GeometricPoint.Hom x x) :
    (rationalInverseImageStalkEquiv B f F x).toLinearMap ∘ₗ
        LAdicSheaf.rationalStalkEnd B X ℓ (LAdicSheaf.inverseImage f F) a =
      LAdicSheaf.rationalStalkEnd B Y ℓ F (a.mapHom (B.inclusion.map f)) ∘ₗ
        (rationalInverseImageStalkEquiv B f F x).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    rationalInverseImageStalkEquiv, LAdicSheaf.rationalStalkEnd_tmul, LinearEquiv.baseChange_tmul]
  exact congrArg _ (inverseImageStalkEquiv_stalkEnd B f F x a v)

/-- **The endomorphism of the geometric point has the same trace on the rational stalk of `f⁻¹F`
at `x̄` as on that of `F` at `f(x̄)`.** -/
public theorem trace_inverseImage_rationalStalkEnd (F : LAdicSheaf B Y ℓ) (x : GeometricPoint X.obj)
    (a : GeometricPoint.Hom x x) :
    LinearMap.trace (Padic ℓ) _
        (LAdicSheaf.rationalStalkEnd B X ℓ (LAdicSheaf.inverseImage f F) a) =
      LinearMap.trace (Padic ℓ) _
        (LAdicSheaf.rationalStalkEnd B Y ℓ F (a.mapHom (B.inclusion.map f))) := by
  rw [← LinearMap.trace_conj' _ (rationalInverseImageStalkEquiv B f F x)]
  congr 1
  refine LinearMap.ext fun w => ?_
  have h := LinearMap.congr_fun (rationalInverseImageStalkEquiv_rationalStalkEnd B f F x a)
    ((rationalInverseImageStalkEquiv B f F x).symm w)
  simpa [LinearEquiv.conj_apply] using h

end Stacks.EtaleCohomology
