module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly
public import StacksFrontier.AlgebraicGeometry.Curves.TwistedFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree

/-!
# Morphisms of finite étale covers from stabilizers, and degrees as fibre counts

Let `X` be a connected scheme with a geometric point `x`, so that finite étale covers of `X` are
finite continuous `π₁(X, x)`-sets (Tag 0BND).

* If the fibre of `V` is the orbit of `v` and every element fixing `v` fixes a point `w` of the
  fibre of `W`, there is a morphism `V ⟶ W` sending `v` to `w`
  (`AlgebraicGeometry.exists_hom_finiteEtaleOver_of_stabilizer_le`): the map `σ v ↦ σ w` of
  fibres is equivariant.
* If `X` is a proper curve over a field and `V` a connected finite étale cover which is again a
  proper curve, the degree of `V ⟶ X` is the number of points of the geometric fibre
  (`AlgebraicGeometry.degreeOver_eq_natCard_finiteEtaleFiber`); for a morphism `V ⟶ W` of such
  covers with transitive fibres, the degree of `V ⟶ W` is the index of the stabilizer of a point
  of `V` in the stabilizer of its image
  (`AlgebraicGeometry.degreeOver_eq_relIndex_stabilizer`).

These are inputs of the effacement of `H²` in the proof of Tag 03VM.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- **A morphism of covers from an inclusion of stabilizers.** If the fibre of `V` at `x` is the
orbit of `v` and every element of `π₁(X, x)` fixing `v` fixes `w` in the fibre of `W`, some
morphism `V ⟶ W` sends `v` to `w`. -/
theorem exists_hom_finiteEtaleOver_of_stabilizer_le (V W : FiniteEtaleOver X)
    (v : (finiteEtaleFiberFunctor x).obj V) (w : (finiteEtaleFiberFunctor x).obj W)
    (hv : ∀ z, ∃ σ : EtaleFundamentalGroup X x, σ • v = z)
    (h : ∀ σ : EtaleFundamentalGroup X x, σ • v = v → σ • w = w) :
    ∃ f : V ⟶ W, (finiteEtaleFiberFunctor x).map f v = w := by
  classical
  choose c hc using hv
  let t : (finiteEtaleFiberFunctor x).obj V → (finiteEtaleFiberFunctor x).obj W :=
    fun z ↦ c z • w
  have ht : ∀ (τ : EtaleFundamentalGroup X x) z, t (τ • z) = τ • t z := by
    intro τ z
    have h1 : ((τ * c z)⁻¹ * c (τ • z)) • v = v := by
      rw [mul_smul, hc, mul_inv_rev, mul_smul, inv_smul_smul]
      exact inv_smul_eq_iff.2 (hc z).symm
    change c (τ • z) • w = τ • c z • w
    calc c (τ • z) • w = (τ * c z) • (((τ * c z)⁻¹ * c (τ • z)) • w) := by
          rw [smul_smul, mul_inv_cancel_left]
      _ = τ • c z • w := by rw [h _ h1, mul_smul]
  let E := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let hAct : (E.functor.obj V).obj ⟶ (E.functor.obj W).obj :=
    { hom := FintypeCat.homMk t
      comm := fun τ ↦ by
        ext z
        change t (ConcreteCategory.hom ((E.functor.obj V).obj.ρ τ).asHom z) =
          ConcreteCategory.hom ((E.functor.obj W).obj.ρ τ).asHom (t z)
        exact (congrArg t (finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply x _ τ z)).trans
          ((ht τ z).trans (finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply x W τ (t z)).symm) }
  let f := E.functor.preimage (ObjectProperty.homMk hAct)
  have hf : E.functor.map f = ObjectProperty.homMk hAct := E.functor.map_preimage _
  have hfv : ConcreteCategory.hom (E.functor.map f).hom.hom v = t v := by
    rw [hf]
    rfl
  exact ⟨f, hfv.trans (h _ (hc v))⟩

/-- On a transitive fibre, the number of points is the index of a stabilizer. -/
theorem natCard_finiteEtaleFiber_eq_index_stabilizer (V : FiniteEtaleOver X)
    (v : (finiteEtaleFiberFunctor x).obj V)
    (hv : ∀ z, ∃ σ : EtaleFundamentalGroup X x, σ • v = z) :
    Nat.card ((finiteEtaleFiberFunctor x).obj V) =
      (MulAction.stabilizer (EtaleFundamentalGroup X x) v).index := by
  have horb : MulAction.orbit (EtaleFundamentalGroup X x) v = Set.univ :=
    Set.eq_univ_of_forall fun z ↦ MulAction.mem_orbit_iff.2 (hv z)
  rw [Subgroup.index, ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ v), horb,
    Nat.card_univ]

section Degree

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

include f in
omit [IsProper f] in
/-- A finite étale cover with nonempty source of a curve is not constant. -/
theorem not_constant_finiteEtaleOver (V : FiniteEtaleOver X) [Nonempty V.left] :
    ¬ ∃ y : X, ∀ z : V.left, V.hom.base z = y := by
  rintro ⟨y, hy⟩
  have hsurj := surjective_of_finiteEtale V
  have := nontrivial_of_isCurve f
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  exact hab ((hy a').trans (hy b').symm)

/-- **The degree of a connected finite étale cover of a curve is the size of a geometric
fibre.** -/
theorem degreeOver_eq_natCard_finiteEtaleFiber (V : FiniteEtaleOver X) [ConnectedSpace V.left]
    [IsProper (V.hom ≫ f)] [IsCurve k (V.hom ≫ f)] :
    @degreeOver V.left X V.hom inferInstance inferInstance
        (locallyOfFiniteType_of_isCurve_comp k (V.hom ≫ f) f V.hom rfl)
        (isDominant_of_not_constant k (V.hom ≫ f) f V.hom (not_constant_finiteEtaleOver f V)) =
      Nat.card ((finiteEtaleFiberFunctor x).obj V) := by
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  set d := Nat.card ((finiteEtaleFiberFunctor x).obj V)
  set E := (Scheme.Modules.pushforward V.hom).obj (SheafOfModules.unit V.left.ringCatSheaf)
  have hE : Stacks.Morphisms.IsFiniteLocallyFreeOfRank V.hom d :=
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber x V
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E d := hE.toIsFiniteLocallyFreeOfRank
  exact ((Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E d
    (genericPoint X)).symm.trans
    (fiberRank_pushforward_unit_genericPoint_eq_degreeOver k (V.hom ≫ f) f V.hom rfl
      (not_constant_finiteEtaleOver f V))).symm

end Degree

end AlgebraicGeometry

end
