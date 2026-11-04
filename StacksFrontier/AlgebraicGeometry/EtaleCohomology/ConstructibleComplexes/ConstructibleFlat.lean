module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic

/-!
# Constructible flat sheaves of modules on the small étale site

A sheaf of `Λ`-modules on the small étale site of a scheme is *constructible flat* if, on a
finite constructible stratification of every affine open, it becomes locally constant with
finite projective values. A finite projective module is finitely generated, so a constructible
flat sheaf is constructible in the sense of Tag 03RW.

The characterization of Tag 03TT says that an object of `D(X_étale, Λ)` belongs to
`D_{ctf}(X_étale, Λ)` exactly when it is represented by a bounded complex of constructible flat
sheaves of `Λ`-modules. The second condition is
`Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatComplex`, and the implication from it to
constructibility of the cohomology sheaves — the half of the direction (2) ⟹ (1) which does not
concern Tor dimension — is proved here.

## Main definitions

* `Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant`: local constancy of a sheaf of
  modules with finite projective values.
* `AlgebraicGeometry.IsConstructibleFlatModuleSheaf`: a constructible flat sheaf of
  `Λ`-modules on the small étale site.
* `AlgebraicGeometry.isConstructibleModuleSheafProperty`: constructibility of a sheaf of
  `Λ`-modules, as a property of objects of the abelian category of all such sheaves.
* `Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatComplex`: condition (2) of Tag 03TT,
  that an object of the derived category is represented by a bounded complex of constructible
  flat sheaves of `Λ`-modules.

## Main results

* `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr` and
  `AlgebraicGeometry.isConstructibleFlatModuleSheaf_congr`: local constancy with finite
  projective values, and flat constructibility, are invariant under isomorphism of sheaves.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant`,
  `AlgebraicGeometry.isStratifiedLocallyConstantWith_isFG_of_isConstructibleFlatModuleSheaf` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`: a
  constructible flat sheaf is constructible.
* `Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex`: an
  object of the derived category represented by a bounded complex of constructible flat sheaves
  of `Λ`-modules has constructible cohomology sheaves, so it lies in the constructible derived
  category of Tag 095W.

## Implementation notes

Flatness is expressed as local constancy with finite projective values rather than through a
flatness predicate on sheaves of modules: over a finite, or more generally a Noetherian local,
coefficient ring a finite flat module is projective, and this is the form in which the source
uses the condition. Local constancy and the constructible stratifications are those of Tag 03RW,
whose `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` is stated for an arbitrary ring, so the
flat condition, the constructibility of Tag 03RW part (3) and the comparison between them are
stated for an arbitrary ring as well: a stratumwise condition on left `Λ`-modules takes no
product of two scalars, and the Noetherian hypothesis of Tag 03RW part (3) enters none of
them.

The cohomology sheaves of a complex of constructible sheaves are constructible because the
constructible sheaves of `Λ`-modules form a weak Serre subcategory: the sheaf of cycles is a
kernel of a map between terms and the cohomology sheaf is a cokernel of a map into it. That
weak Serre property is Tag 03RZ (3),
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`, proved at the
coefficient universe `max (u + 1) w` and not below, because Tag 093U (3) does not absorb the
ring universe on the small étale site of Tag 021B. The statement of (2) ⟹ (1) here is at a free
coefficient universe `ModuleCat.{w} Λ`, so it carries the property as the hypothesis `hSerre`;
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty` discharges it at
`max (u + 1) r`, which is where the rest of the chapter works.

The Tor-dimension half of the direction (2) ⟹ (1), that a bounded complex of flat sheaves has
locally finite Tor dimension in the sense of Tag 08FZ over the constant coefficient ringed site
of Tag 03TR, rests on two facts. By
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
each term of a constructible flat complex is a *flat* sheaf of modules over the constant
coefficient ring sheaf, and by
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative` (Tag 08G1) a
bounded complex of flat modules has bounded Tor amplitude. The predicates
`Stacks.SheafOfModules.IsFlat` and `AlgebraicGeometry.SheafOfModules.IsFlat` are definitionally
equal. The degreewise restriction of a flat complex to a slice is again flat (Tag 0E8J, at a free
module universe: `Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over`), which
gives the slicewise form asked for by
`Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension`. That half is proved in
the sibling file `ConstructibleFlatFiniteTor.lean`, which combines it with the statement here into
membership of `D_{ctf}(X_étale, Λ)`.

What remains unproved of Tag 03TT is the converse direction (1) ⟹ (2), whose proof is an induction
on the length of the Tor window resolving the top cohomology sheaf by extensions by zero. The route
that this development's vocabulary suggests instead — pass from locally finite Tor dimension to one
global Tor-amplitude interval `[a, b]`, then truncate the bounded above constructible flat
resolution of Tag 0960 at `a`, Tag 08G0 leaving `Coker(d^{a-1})` flat — is blocked at the passage
to a global interval:
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`
is stated on a `AlgebraicGeometry.RingedSite.{c, u, u}` with `C` essentially `u`-small, so it does
not apply to the constant coefficient ringed site, a
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`. That pin is inherited from
Stacks 0E8K, of which no free-module-universe counterpart has a declaration in this tree.

The universes of the scheme, of the module sections and of the coefficient ring are independent.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w v c r

namespace Stacks.ConstantSheaf

/-- A locally constant sheaf of `R`-modules with finite projective constant values on a
covering of every object of a site. This is the flat case of local constancy: over a ring on
which a finite flat module is projective — a finite ring, for instance — it is flatness of the
constant values together with their finiteness. -/
public abbrev IsFiniteProjectiveLocallyConstant (R : Type r) [Ring R]
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    (F : Sheaf J (ModuleCat.{w} R)) : Prop :=
  ∀ U : C, ∃ (I : Type (max c v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{w} R, Module.Finite R E ∧ Module.Projective R E ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{w} R)).obj E ≅
          (J.overPullback (ModuleCat.{w} R) (V i)).obj F)

/-- A sheaf of modules which is locally constant with finite projective values is locally
constant of finite type: a finite projective module is finitely generated. -/
public theorem isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant
    (R : Type r) [Ring R] {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    {F : Sheaf J (ModuleCat.{w} R)} (hF : IsFiniteProjectiveLocallyConstant R J F) :
    IsFiniteTypeLocallyConstant R J F := by
  intro U
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i => ?_⟩
  obtain ⟨E, hfin, -, he⟩ := hloc i
  exact ⟨E, hfin, he⟩

/-- Local constancy with finite projective values is invariant under isomorphism: the same
covering and the same constant values work, composed with the isomorphism. -/
public theorem isFiniteProjectiveLocallyConstant_congr (R : Type r) [Ring R]
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    {F G : Sheaf J (ModuleCat.{w} R)} (e : F ≅ G)
    (hF : IsFiniteProjectiveLocallyConstant R J F) :
    IsFiniteProjectiveLocallyConstant R J G := by
  intro U
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i => ?_⟩
  obtain ⟨E, hfin, hproj, ⟨eE⟩⟩ := hloc i
  exact ⟨E, hfin, hproj, ⟨eE ≪≫ (J.overPullback (ModuleCat.{w} R) (V i)).mapIso e⟩⟩

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- A **constructible flat sheaf of `Λ`-modules** on the small étale site: on a finite
constructible stratification of every affine open it is locally constant with finite projective
values. The stratifications are those of Tag 03RW. -/
public abbrev IsConstructibleFlatModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- A sheaf isomorphic to a flat constructible sheaf of `Λ`-modules is flat constructible: the
same stratification works, since restriction to a stratum carries the isomorphism along. -/
public theorem isConstructibleFlatModuleSheaf_congr
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)} (e : F ≅ G)
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) : IsConstructibleFlatModuleSheaf B X Λ G := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso e) (hs i)

/-- A constructible flat sheaf of `Λ`-modules is stratumwise locally constant with finitely
generated values: a finite projective module is finitely generated.  No commutativity or
Noetherian hypothesis enters, which is what makes this the form of constructibility the stalk
machinery uses over a general coefficient ring; over a Noetherian commutative ring it is
constructibility in the sense of Tag 03RW part (3), by
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`. -/
public theorem isStratifiedLocallyConstantWith_isFG_of_isConstructibleFlatModuleSheaf
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsStratifiedLocallyConstantWith B X Λ (ModuleCat.isFG Λ) F := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i =>
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant _ _
      (hs i)⟩

/-- A constructible flat sheaf of `Λ`-modules is constructible: on each stratum its finite
projective constant values are finitely generated. -/
public theorem isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) : IsConstructibleModuleSheaf B X Λ F :=
  isStratifiedLocallyConstantWith_isFG_of_isConstructibleFlatModuleSheaf B X Λ hF

variable [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]

/-- Constructibility of a sheaf of `Λ`-modules on the small étale site of `X`, as a property of
objects of the abelian category of all such sheaves. This is the subject of Tag 03RW part (3). -/
public def isConstructibleModuleSheafProperty :
    ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :=
  fun F => IsConstructibleModuleSheaf B X Λ F

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]

/-- **Condition (2) of Tag 03TT.** An object of the unbounded derived category of small-étale
sheaves of `Λ`-modules is represented by a bounded complex of constructible flat sheaves of
`Λ`-modules.

The coefficient ring is arbitrary. Flat constructibility,
`AlgebraicGeometry.IsConstructibleFlatModuleSheaf`, is stratumwise local constancy with finite
projective values, a condition on left `Λ`-modules in which no product of two scalars is taken;
so this condition, unlike the Tor-dimension formulation of Tag 03TQ, is available for the finite
and possibly noncommutative coefficient rings of the trace formula. -/
@[sga "4½ Rapport 4.6"]
public def IsRepresentedByConstructibleFlatComplex
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) : Prop :=
  ∃ (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) (a b : ℤ),
    C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K)

/-- **Tag 03TT, the direction (2) ⟹ (1) for the constructible-cohomology condition.** An
object of `D(X_étale, Λ)` represented by a bounded complex of constructible flat sheaves of
`Λ`-modules has constructible cohomology sheaves, so it lies in the constructible derived
category of Tag 095W.

The cohomology sheaf in degree `i` is a cokernel of a map from the term in degree `i - 1` into
the sheaf of cycles, which is a kernel of a map between the terms in degrees `i` and `i + 1`;
each term is constructible, and the hypothesis `hSerre` that the constructible sheaves of
`Λ`-modules form a weak Serre subcategory of all sheaves of `Λ`-modules — Tag 0754, closure
under kernels, cokernels, extensions and isomorphism — carries constructibility to the kernel
and then to the cokernel. -/
@[stacks 03TT "the direction (2) => (1), the constructible-cohomology half, from the weak \
Serre property `hSerre` of the constructible sheaves of modules"]
public theorem isConstructible_of_isRepresentedByConstructibleFlatComplex
    (hSerre : (isConstructibleModuleSheafProperty.{u, w, r} B X Λ).IsWeakSerreClass)
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, w, r} B X Λ K) :
    IsConstructible B X Λ K := by
  have := hSerre
  set P := isConstructibleModuleSheafProperty.{u, w, r} B X Λ
  obtain ⟨C, -, -, -, -, hC, ⟨e⟩⟩ := hK
  have hterm : ∀ j : ℤ, P (C.X j) := fun j =>
    isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hC j)
  intro i
  have hcycles : P (C.cycles i) :=
    P.prop_of_isLimit_kernelFork (C.cyclesIsKernel i (i + 1) (by simp))
      (hterm i) (hterm (i + 1))
  have hhomology : P (C.homology i) :=
    P.prop_of_isColimit_cokernelCofork (C.homologyIsCokernel (i - 1) i (by simp))
      (hterm (i - 1)) hcycles
  exact P.prop_of_iso
    (((DerivedCategory.homologyFunctorFactors
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) i).app C).symm ≪≫
      (DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) i).mapIso e)
    hhomology

end Stacks.EtaleCohomology

end
