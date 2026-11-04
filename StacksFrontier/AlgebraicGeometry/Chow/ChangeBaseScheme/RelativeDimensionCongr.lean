module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionFlatPullback

/-!
# Chow groups depend only on the relative dimension function

The groups of `k`-cycles and of `k`-cycles rationally equivalent to zero on a scheme `X` locally
of finite type over the base of a `Stacks.Chow.ChowSituation` are defined from the scheme `X`
and the relative dimension function that the dimension function of the base induces on `X` and
its closed subschemes; nothing else about the base enters. So two structure morphisms
`f : X ⟶ C.S` and `f' : X ⟶ D.S` that induce the same relative dimension on every closed
subscheme of `X` give the same cycle groups and the same subgroups of cycles rationally
equivalent to zero, hence isomorphic Chow groups, by an isomorphism that is the identity on
coefficient functions.

The case used in the chapter on Weil cohomology theories is a scheme `X` over a finite extension
`k'/k`: its Chow groups over `k'` and over `k`, through `Spec k' ⟶ Spec k`, agree. This is how
`CH_0(X)` of a smooth projective scheme over `k'`, the group of Stacks 0FHU, is identified with
the group of zero cycles of `X` as a scheme over `k`.

## Main definitions

* `Stacks.Chow.cycleGroupEquivOfRelativeDimension`: `Z_k(X)` for `f` and for `f'` are the same.
* `Stacks.Chow.chowGroupEquivOfRelativeDimension`: so are `A_k(X)`.
* `Stacks.Chow.chowGroupFiniteExtensionEquiv`: the Chow groups of a scheme over a finite
  extension `k'/k`, over `k'` and over `k`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {C D : ChowSituation.{u}} {X : Scheme.{u}} (f : X ⟶ C.S) (f' : X ⟶ D.S)
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']

/-- Two structure morphisms induce **the same relative dimension on every closed subscheme**. -/
def SameRelativeDimension : Prop :=
  ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i],
    relativeDimension D.dimensionFunction (i ≫ f') =
      relativeDimension C.dimensionFunction (i ≫ f)

variable {f f'}

omit [LocallyOfFiniteType f] [LocallyOfFiniteType f'] in
/-- With the same relative dimensions, the relative dimension on `X` itself is the same. -/
theorem SameRelativeDimension.apply (h : SameRelativeDimension f f') :
    relativeDimension D.dimensionFunction f' = relativeDimension C.dimensionFunction f := by
  simpa using h X (𝟙 X)

/-- With the same relative dimensions, every closed subscheme has the same delta-dimension. -/
theorem SameRelativeDimension.schemeDeltaDimension_eq (h : SameRelativeDimension f f')
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    schemeDeltaDimension D (i ≫ f') = schemeDeltaDimension C (i ≫ f) := by
  simp only [schemeDeltaDimension_eq_iSup, deltaDimension, h Z i]

/-- With the same relative dimensions, the pushforward of a principal divisor along an integral
closed subscheme is the same cycle. -/
theorem SameRelativeDimension.principalDivisorPushforward_eq (h : SameRelativeDimension f f')
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) :
    principalDivisorPushforward D f' V hV g = principalDivisorPushforward C f V hV g := by
  simp only [principalDivisorPushforward, h _ V.subschemeι, h.apply]

variable (f f')

/-- **The cycle groups of two structure morphisms with the same relative dimensions** are the
same subgroup of the group of cycles of `X`. -/
def cycleGroupEquivOfRelativeDimension (h : SameRelativeDimension f f') (k : ℤ) :
    CycleGroup C f k ≃+ CycleGroup D f' k where
  toFun z := ⟨z.1, by
    rw [mem_cyclesOfDimension_iff_forall_point, h.apply]
    exact (mem_cyclesOfDimension_iff_forall_point C f k z.1).1 z.2⟩
  invFun z := ⟨z.1, by
    rw [mem_cyclesOfDimension_iff_forall_point, ← h.apply]
    exact (mem_cyclesOfDimension_iff_forall_point D f' k z.1).1 z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The isomorphism `cycleGroupEquivOfRelativeDimension` is the identity on underlying cycles. -/
@[simp]
theorem cycleGroupEquivOfRelativeDimension_apply_coe (h : SameRelativeDimension f f') (k : ℤ)
    (z : CycleGroup C f k) : (cycleGroupEquivOfRelativeDimension f f' h k z).1 = z.1 :=
  rfl

/-- With the same relative dimensions, a cycle is rationally equivalent to zero for one
structure morphism exactly when it is for the other: the families of integral closed
subschemes, their delta-dimensions and the pushforwards of principal divisors are the same. -/
theorem mem_rationalEquivalences_iff_of_relativeDimension (h : SameRelativeDimension f f')
    (k : ℤ) (z : CycleGroup C f k) :
    cycleGroupEquivOfRelativeDimension f f' h k z ∈ rationalEquivalences D f' k ↔
      z ∈ rationalEquivalences C f k := by
  simp only [mem_rationalEquivalences, isRationallyEquivalentToZero_iff,
    cycleGroupEquivOfRelativeDimension_apply_coe, principalDivisorFamilyCoefficient,
    h.principalDivisorPushforward_eq, h.schemeDeltaDimension_eq]

/-- **The Chow groups of two structure morphisms with the same relative dimensions** agree, by
the identity on representing cycles. -/
def chowGroupEquivOfRelativeDimension (h : SameRelativeDimension f f') (k : ℤ) :
    chowGroup C f k ≃+ chowGroup D f' k :=
  QuotientAddGroup.congr _ _ (cycleGroupEquivOfRelativeDimension f f' h k) <| by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_rationalEquivalences_iff_of_relativeDimension f f' h k w).2 hw
    · intro hz
      exact ⟨(cycleGroupEquivOfRelativeDimension f f' h k).symm z,
        (mem_rationalEquivalences_iff_of_relativeDimension f f' h k _).1
          (by rwa [AddEquiv.apply_symm_apply]), AddEquiv.apply_symm_apply _ z⟩

/-- The isomorphism `chowGroupEquivOfRelativeDimension` sends the class of a cycle to the class
of the same cycle. -/
@[simp]
theorem chowGroupEquivOfRelativeDimension_mk (h : SameRelativeDimension f f') (k : ℤ)
    (z : CycleGroup C f k) :
    chowGroupEquivOfRelativeDimension f f' h k
        (QuotientAddGroup.mk' (rationalEquivalences C f k) z) =
      QuotientAddGroup.mk' (rationalEquivalences D f' k)
        (cycleGroupEquivOfRelativeDimension f f' h k z) :=
  rfl

/-- With the same relative dimensions, the cycle of a closed subscheme is the same cycle. -/
theorem cycleGroupEquivOfRelativeDimension_cycleAssociatedToClosedSubscheme
    (h : SameRelativeDimension f f') {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (k : ℤ) :
    cycleGroupEquivOfRelativeDimension f f' h k (cycleAssociatedToClosedSubscheme C f i k) =
      cycleAssociatedToClosedSubscheme D f' i k := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  simp only [cycleGroupEquivOfRelativeDimension_apply_coe, cycleAssociatedToClosedSubscheme,
    closedSubschemeCycle]
  show closedSubschemeCycleCoeff C f i k x = closedSubschemeCycleCoeff D f' i k x
  have hx : relativeDimension D.dimensionFunction f' x =
      relativeDimension C.dimensionFunction f x := congrFun h.apply x
  unfold closedSubschemeCycleCoeff
  generalize relativeDimension C.dimensionFunction f x = r at hx ⊢
  subst hx
  rfl

/-! ### A finite extension of the base field -/

/-- The morphism `Spec k' ⟶ Spec k` of a field extension `k'/k`. -/
abbrev fieldExtensionSpecMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (fieldChowSituation k').S ⟶ (fieldChowSituation k).S :=
  (fieldExtensionBaseChangeSituation k k').g

/-- For a finite extension `k'/k`, the morphism `Spec k' ⟶ Spec k` is locally of finite type. -/
instance (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k'] :
    LocallyOfFiniteType (fieldExtensionSpecMap k k') := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  infer_instance

/-- Over a finite extension `k'/k`, the relative dimensions of a scheme over `k'` computed over
`k'` and over `k` agree, on every closed subscheme. -/
theorem sameRelativeDimension_fieldExtension (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (p : X ⟶ (fieldChowSituation k').S) [LocallyOfFiniteType p] :
    SameRelativeDimension p (p ≫ fieldExtensionSpecMap k k') := by
  intro Z i _
  funext z
  rw [← Category.assoc]
  exact relativeDimension_comp_fieldExtension k k' (i ≫ p) z

/-- **The Chow groups of a scheme over a finite extension `k'/k`**, computed over `k'` and over
`k` through `Spec k' ⟶ Spec k`, agree. -/
def chowGroupFiniteExtensionEquiv (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (p : X ⟶ (fieldChowSituation k').S) [LocallyOfFiniteType p]
    (n : ℤ) :
    chowGroup (fieldChowSituation k') p n ≃+
      chowGroup (fieldChowSituation k) (p ≫ fieldExtensionSpecMap k k') n :=
  chowGroupEquivOfRelativeDimension _ _ (sameRelativeDimension_fieldExtension k k' p) n

end Stacks.Chow

end
