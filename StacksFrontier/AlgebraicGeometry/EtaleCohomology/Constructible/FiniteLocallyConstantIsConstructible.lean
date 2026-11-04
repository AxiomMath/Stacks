module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability

/-!
# A finite locally constant sheaf is constructible

A sheaf on the small étale site of a scheme which is finite locally constant — or, for sheaves
of modules over a Noetherian ring, locally constant with finitely generated values — is
constructible: on every affine open the one-stratum partition works.

The one stratum is the affine open itself, carrying the reduced induced subscheme structure
supplied by `AlgebraicGeometry.ConstructibleStratification.ofPartition`. The condition on that
stratum is about the *inverse image* of the sheaf along the stratum's immersion, not about the
sheaf itself, so the statement is not a tautology: what discharges it is that finite local
constancy survives inverse image along an arbitrary morphism of the big étale site,
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback'`.

Beyond being the degenerate case of Tag 095E (3) ⇒ (1), this is the fact that makes the
constructibility predicates **non-vacuous**: without it, nothing exhibits a sheaf satisfying
`AlgebraicGeometry.IsConstructibleSetSheaf` at all, and every theorem taking constructibility as
a hypothesis could be vacuous.

## Main results

* `AlgebraicGeometry.isConstructibleFiniteSheaf_of_isFiniteLocallyConstant` — the statement for
  an arbitrary concrete coefficient category, hence for sheaves of sets and of abelian groups at
  once.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_isFiniteLocallyConstant` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_isFiniteLocallyConstant` — its two
  specializations.
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant` — the statement
  for sheaves of modules over a Noetherian ring, where the stratum condition is local constancy
  with finitely generated values.

## Implementation notes

No declaration here carries a Stacks tag. Tag 03RW is the definition of constructibility and is
attributed where the predicates are defined; Tag 095E is the equivalence of constructibility with
Zariski-local constructibility and with the existence of one global stratification, and is
attributed where those equivalences are proved. What is proved here is the special case of one
stratum, which is an input to the latter rather than any part of it.

The concrete statement is stated with the coefficient universe of
`AlgebraicGeometry.IsConstructibleFiniteSheaf`, independent of the scheme universe, so the
scheme-dependent specializations follow by instantiation.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w t r u

namespace AlgebraicGeometry

/-- The partition of an open `U` with the single member `U`, as a constructible stratification. -/
private noncomputable def oneStratum (B : BigEtaleSite.{u}) (X : B.Scheme) (U : X.obj.Opens) :
    ConstructibleStratification B X U :=
  ConstructibleStratification.ofPartition B X U
    (fun _ : Fin 1 => (U : Set X.obj))
    (fun _ => U.isOpen.isLocallyClosed) (fun _ => subset_rfl)
    (fun _ => by
      rw [Set.preimage_eq_univ_iff.2 (by rw [Scheme.Opens.range_ι])]
      exact Topology.IsConstructible.univ)
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (Set.iUnion_const _).symm

section Concrete

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {D : Type w} [Category.{v} D]
  {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- **A finite locally constant sheaf with values in a concrete category is constructible.** On
an affine open the partition with the single member that affine open satisfies the defining
condition, because finite local constancy survives the inverse image along the immersion of that
member with its reduced induced structure. -/
public theorem isConstructibleFiniteSheaf_of_isFiniteLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D)
    [hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FD) (CD := CD)
      (SmallEtale.topology B X.obj X.property) F] :
    IsConstructibleFiniteSheaf B X F := by
  intro U
  exact ⟨oneStratum B X U.1, fun i => isFiniteLocallyConstant_smallEtaleSheafPullback' B D _ F⟩

end Concrete

section Sets

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **A finite locally constant sheaf of sets is constructible.** -/
public theorem isConstructibleSetSheaf_of_isFiniteLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B X.obj X.property) F] :
    IsConstructibleSetSheaf B X F :=
  isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B X F

end Sets

section Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]

/-- **A finite locally constant sheaf of abelian groups is constructible.** -/
public theorem isConstructibleAbelianSheaf_of_isFiniteLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B X.obj X.property) F] :
    IsConstructibleAbelianSheaf B X F :=
  isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B X F

end Abelian

section Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [Ring R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

omit [IsNoetherianRing R] in
/-- **A sheaf of modules which is locally constant with finitely generated values is
constructible.** No Noetherian hypothesis on the ring is needed. The stratum condition of
`AlgebraicGeometry.IsConstructibleModuleSheaf` is local constancy of finite type rather than
finite local constancy, so this is not an instance of the concrete statement above; the stratum
is the same one and the input is the corresponding stability of local constancy of finite type
under inverse image. -/
public theorem isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B X.obj X.property) F) :
    IsConstructibleModuleSheaf B X R F := by
  intro U
  exact ⟨oneStratum B X U.1,
    fun i => isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R _ F hF⟩

end Modules

end AlgebraicGeometry

end
