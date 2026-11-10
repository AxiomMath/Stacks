module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients

/-!
# The levels of an ℓ-adic sheaf with flat levels are constructible flat

A sheaf of modules on the small étale site of a scheme which is locally constant with finitely
generated values, and whose stalks at all geometric points are projective, is locally constant
with finite projective values: a local value over a nonempty étale neighbourhood is the stalk at
a geometric point of that neighbourhood, and over an empty one the sheaf is zero.  Applied on the
strata of a constructible stratification, whose stalks are stalks of the original sheaf, this
shows that the levels `Fₙ` of an ℓ-adic sheaf whose levels are flat over `ℤ/ℓⁿ⁺¹ℤ` are
constructible flat `ℤ/ℓⁿ⁺¹ℤ`-modules, as in Tags 03UV and 03UZ.

## Main results

* `AlgebraicGeometry.isFiniteProjectiveLocallyConstant_of_projective_etaleStalk`: the local
  statement.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_projective_etaleStalk`: a constructible
  sheaf with projective stalks is constructible flat.
* `Stacks.EtaleCohomology.LAdicSheaf.isConstructibleFlatModuleSheaf_level`: the levels of an ℓ-adic
  sheaf with flat levels are constructible flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u z uC vC uA vA

namespace AlgebraicGeometry

/-! ### Local values with projective stalks -/

section Local

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (Y : B.Scheme) (R : Type) [CommRing R]

/-- Over an object of the small étale site with empty underlying scheme, every sheaf on the slice
site is zero: every object of the slice is covered by the empty sieve. -/
theorem isZero_of_isEmpty_toScheme {V : SmallEtale B Y.obj Y.property}
    (hV : IsEmpty ((SmallEtale.toScheme B Y.obj Y.property).obj V))
    (H : Sheaf ((SmallEtale.topology B Y.obj Y.property).over V) (ModuleCat.{u + 1} R)) :
    IsZero H := by
  have hbot : ∀ W : Over V, (⊥ : Sieve W) ∈ (SmallEtale.topology B Y.obj Y.property).over V W := by
    intro W
    rw [GrothendieckTopology.mem_over_iff]
    have hW : IsEmpty ((SmallEtale.toScheme B Y.obj Y.property).obj W.left) :=
      ⟨fun w => hV.false ((SmallEtale.toScheme B Y.obj Y.property).map W.hom w)⟩
    simpa using Stacks.EtaleCohomology.bot_mem_topology B Y.property hW
  refine (IsZero.iff_id_eq_zero _).2 (Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_)))
  exact (Sheaf.isTerminalOfBotCover H (unop W) (hbot (unop W))).hom_ext _ _

variable
  [∀ V : SmallEtale B Y.obj Y.property,
    HasWeakSheafify ((SmallEtale.topology B Y.obj Y.property).over V) (ModuleCat.{u + 1} R)]

/-- **A locally constant sheaf of finite type with projective stalks is locally constant with
finite projective values.** -/
theorem isFiniteProjectiveLocallyConstant_of_projective_etaleStalk
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} R))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B Y.obj Y.property) G)
    (hstalk : ∀ s : GeometricPoint Y.obj,
      Module.Projective R (etaleStalk (A := ModuleCat.{u + 1} R) B Y.obj Y.property s G.obj)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant R
      (SmallEtale.topology B Y.obj Y.property) G := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hG U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hV i
  by_cases hemp : IsEmpty ((SmallEtale.toScheme B Y.obj Y.property).obj (V i))
  · exact ⟨ModuleCat.of R PUnit, inferInstance, inferInstance,
      ⟨(isZero_of_isEmpty_toScheme B Y R hemp _).iso (isZero_of_isEmpty_toScheme B Y R hemp _)⟩⟩
  · obtain ⟨v⟩ := not_isEmpty_iff.1 hemp
    let t :=
      Stacks.Frobenius.geometricPointAt ((SmallEtale.toScheme B Y.obj Y.property).obj (V i)) v
    let s : GeometricPoint Y.obj := t.map (B.inclusion.map (V i).obj.hom)
    let p := geometricPointSitePoint B Y.obj Y.property s
    let y : p.fiber.obj (V i) := ⟨t.hom, rfl⟩
    let eE : E ≅ etaleStalk (A := ModuleCat.{u + 1} R) B Y.obj Y.property s G.obj :=
      (constantSheafFiberIso (p.over y) E).symm ≪≫
        (p.over y).sheafFiber.mapIso e ≪≫ overPullbackSheafFiberIso p y G
    have := hstalk s
    exact ⟨E, by rwa [ModuleCat.isFG_iff] at hE, Module.Projective.of_equiv eE.symm.toLinearEquiv,
      ⟨e⟩⟩

end Local

/-! ### Constructible sheaves with projective stalks -/

section Global

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type) [CommRing R]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} R)]

/-- **A constructible sheaf of modules whose stalks are projective is constructible flat.** On
each stratum the restriction is locally constant of finite type, and its stalks are stalks of the
sheaf, hence projective. -/
theorem isConstructibleFlatModuleSheaf_of_projective_etaleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F)
    (hstalk : ∀ s : GeometricPoint X.obj,
      Module.Projective R (etaleStalk (A := ModuleCat.{u + 1} R) B X.obj X.property s F.obj)) :
    IsConstructibleFlatModuleSheaf B X R F := by
  intro U
  obtain ⟨σ, hσ⟩ := hF U
  refine ⟨σ, fun i => isFiniteProjectiveLocallyConstant_of_projective_etaleStalk B (σ.piece i) R
    _ (hσ i) fun t => ?_⟩
  have := hstalk (t.map (B.inclusion.map (σ.inclusion i)))
  exact Module.Projective.of_equiv
    (etaleStalkSmallEtalePullObjIso B (σ.inclusion i) t (ModuleCat.{u + 1} R) F).symm.toLinearEquiv

end Global

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory.Abelian

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]

/-- The finite-level stalks of an ℓ-adic sheaf with flat levels are finite projective
`ℤ/ℓⁿ⁺¹ℤ`-modules: finite, and flat over a local ring. -/
theorem LAdicSheaf.projective_finiteLevelStalk (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (s : GeometricPoint X.1) (n : ℕ) :
    Module.Projective (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F s n) := by
  have := zmod_pow_succ_isLocalRing (ℓ := ℓ) n
  have : Finite (finiteLevelStalk B X ℓ F s n) := finite_finiteLevelStalk B X ℓ F s n
  have : Module.Finite (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F s n) :=
    Module.Finite.of_finite
  have : Module.Flat (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F s n) :=
    Stacks.ZModPrimePower.flat_of_isPowExact (LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n))
  have : Module.Free (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F s n) :=
    Module.free_of_flat_of_isLocalRing
  infer_instance

/-- **The levels of an ℓ-adic sheaf with flat levels are constructible flat** `ℤ/ℓⁿ⁺¹ℤ`-modules,
so that the L-function of Tag 03UV and the cohomological interpretation of Tag 03UZ apply to
them. -/
theorem LAdicSheaf.isConstructibleFlatModuleSheaf_level (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (n : ℕ) :
    IsConstructibleFlatModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (F.level n) :=
  isConstructibleFlatModuleSheaf_of_projective_etaleStalk B X _ (F.level n) (F.constructible n)
    fun s => LAdicSheaf.projective_finiteLevelStalk B X ℓ F hF s n

end Stacks.EtaleCohomology

end
