module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat

/-!
# The stalks of a constructible flat sheaf of modules

A constructible flat sheaf of `Λ`-modules on the small étale site of `X` is, on each stratum of a
constructible stratification of each affine open, locally constant with finite projective values.
Its stalk at a geometric point is therefore one of those values, up to isomorphism, hence a
finite projective `Λ`-module; and the stalk of a bounded complex of such sheaves is a perfect
object of `D(Λ)`.

This is the content [Stacks, Tag 03TR] contributes to the characterization of
`D_{ctf}(X_étale, Λ)` in [Stacks, Tag 03TT]: the hypothesis of
`AlgebraicGeometry.stalk_isPerfect` is flatness over the constant coefficient ring sheaf of
[Stacks, Tag 03TR], which is a condition on the sheaf of modules obtained by sheafifying the
action of the constant sections, whereas condition (2) of Tag 03TT is constructible flatness of
the terms.  The results here read the perfection of the stalk complex off the latter, with no
flatness hypothesis on the associated sheaf of modules.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstantWith_projective_of_isFiniteProjectiveLocallyConstant`
  — a locally constant sheaf of modules with finite projective values is locally constant with
  projective values.
* `AlgebraicGeometry.isStratifiedLocallyConstantWith_projective_of_isConstructibleFlatModuleSheaf`
  — a constructible flat sheaf of modules is stratumwise locally constant with projective values.
* `AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf` — **the stalk
  at a geometric point of a constructible flat sheaf of `Λ`-modules is a projective
  `Λ`-module.**
* `AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf` — **the stalk at a
  geometric point of a bounded complex of constructible flat sheaves of `Λ`-modules is a perfect
  object of `D(Λ)`.**

## Implementation notes

Projectivity alone is what the stalk machinery needs, so the predicate carried through
`AlgebraicGeometry.stalk_prop_of_isStratifiedLocallyConstantWith` is projectivity and not
projectivity together with finiteness: a subsingleton module is free, hence projective, which is
the hypothesis `hQzero` of that theorem, and projectivity transfers along an isomorphism of
modules, which is `hQiso`.  Finiteness of the stalk is then
`AlgebraicGeometry.stalk_finite`, applied to the constructibility of a constructible flat sheaf,
and perfection of the stalk complex is
`AlgebraicGeometry.stalk_isPerfect_of_finite_projective`.

The coefficient ring is an arbitrary, possibly noncommutative, ring throughout, which is what
the finite ring `Λ` of [Stacks, Tag 03TX] means.  Nothing in the chain needs more: local
constancy with finite projective values is a condition on left `Λ`-modules,
`AlgebraicGeometry.stalk_finite` asks for stratumwise local constancy with finitely generated
values rather than for the predicate of Tag 03RW part (3) — which fixes a Noetherian
commutative ring — and the perfection criterion
`AlgebraicGeometry.stalk_isPerfect_of_finite_projective` only carries the degree bounds across
an additive functor.  Commutativity is needed exactly where flatness over the constant
coefficient ring sheaf is, namely in `AlgebraicGeometry.stalk_isPerfect` and not here.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w v c r

namespace Stacks.ConstantSheaf

/-- A sheaf of modules which is locally constant with finite projective values is locally
constant with projective values. -/
public theorem isLocallyConstantWith_projective_of_isFiniteProjectiveLocallyConstant
    (R : Type r) [Ring R] {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    {F : Sheaf J (ModuleCat.{w} R)} (hF : IsFiniteProjectiveLocallyConstant R J F) :
    IsLocallyConstantWith R J (fun E : ModuleCat.{w} R => Module.Projective R E) F := by
  intro U
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i => ?_⟩
  obtain ⟨E, -, hproj, he⟩ := hloc i
  exact ⟨E, hproj, he⟩

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- A constructible flat sheaf of `Λ`-modules is, on each stratum of a constructible
stratification of each affine open, locally constant with projective values. -/
public theorem isStratifiedLocallyConstantWith_projective_of_isConstructibleFlatModuleSheaf
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsStratifiedLocallyConstantWith B X Λ
      (fun E : ModuleCat.{w} Λ => Module.Projective Λ E) F := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i =>
    Stacks.ConstantSheaf.isLocallyConstantWith_projective_of_isFiniteProjectiveLocallyConstant
      _ _ (hs i)⟩

variable [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- **The stalk of a constructible flat sheaf of `Λ`-modules is projective.** On the stratum
through the image of the geometric point the sheaf is locally constant with finite projective
values, so the stalk is one of those values up to isomorphism; a subsingleton module is free,
hence projective, which covers the degenerate case. -/
public theorem etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (s : GeometricPoint X.obj) :
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F) :=
  stalk_prop_of_isStratifiedLocallyConstantWith B X Λ
    (fun E : ModuleCat.{w} Λ => Module.Projective Λ E)
    (fun e hE => have := hE; Module.Projective.of_equiv' e.toLinearEquiv)
    (fun _ hE => have := hE; inferInstance)
    F (isStratifiedLocallyConstantWith_projective_of_isConstructibleFlatModuleSheaf B X Λ hF) s

/-- **The stalk of a bounded complex of constructible flat sheaves of `Λ`-modules is perfect.**
The stalk modules are finite, by `AlgebraicGeometry.stalk_finite` applied to the
constructibility of a constructible flat sheaf, and projective, by
`AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf`; the
perfection criterion `AlgebraicGeometry.stalk_isPerfect_of_finite_projective` concludes.

Unlike `AlgebraicGeometry.stalk_isPerfect` this asks nothing of the sheaf of modules over the
constant coefficient ring sheaf, so it applies directly to the terms of a complex satisfying
condition (2) of [Stacks, Tag 03TT]. -/
public theorem stalk_isPerfect_of_isConstructibleFlatModuleSheaf
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hbounded : (CochainComplex.plus _ K) ∧ (CochainComplex.minus _ K))
    (hflat : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (K.X i))
    (s : GeometricPoint X.obj)
    [HasDerivedCategory (ModuleCat.{w} Λ)] :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (etaleModuleStalkComplex B X Λ s K)) :=
  stalk_isPerfect_of_finite_projective B X Λ K hbounded s
    (fun i => stalk_finite B X Λ K
      (fun j => isStratifiedLocallyConstantWith_isFG_of_isConstructibleFlatModuleSheaf B X Λ
        (hflat j))
      s i)
    (fun i => etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ (K.X i)
      (hflat i) s)

end AlgebraicGeometry

end
