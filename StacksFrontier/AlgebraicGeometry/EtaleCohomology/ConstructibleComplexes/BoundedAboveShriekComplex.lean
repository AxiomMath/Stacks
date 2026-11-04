module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekCoverOfCohomology

/-!
# Bounded above complexes of shriek sums and of flat constructible sheaves

Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian ring and let
`K ∈ D^-(X_étale, Λ)`. Tag 0960 asserts the equivalence of

1. `K` lies in `D_c(X_étale, Λ)`, i.e. all cohomology sheaves of `K` are constructible;
2. `K` is represented by a bounded above complex whose terms are finite direct sums of sheaves
   `j_{U!} Λ-underline` with `U` an affine object of `X_étale`;
3. `K` is represented by a bounded above complex of flat constructible sheaves of `Λ`-modules.

The two conditions which are not already available are written here, and the implications
(2) ⟹ (3), (3) ⟹ (1) and hence (2) ⟹ (1) are proved. The source calls the chain
(2) ⟹ (3) ⟹ (1) immediate; the content of the tag is the converse (1) ⟹ (2), which is proved
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution`,
together with the equivalence itself, see "Where the converse is proved" below. What is proved of
it here is the step the source's descending induction iterates, together with the homological
algebra of a distinguished triangle which that step needs.

## Main definitions

* `Stacks.EtaleCohomology.IsRepresentedByAffineShriekSumComplex` — condition (2).
* `Stacks.EtaleCohomology.IsRepresentedByBoundedAboveConstructibleFlatComplex` — condition (3).

## Main results

* `Stacks.Homology.isZero_homology_obj₃_of_distTriang` and
  `Stacks.Homology.prop_homology_obj₃_of_distTriang` — vanishing of, and membership in a weak
  Serre subcategory of, the cohomology of the third vertex of a distinguished triangle in the
  derived category of an arbitrary abelian category.
* `AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty` — Tag 03RZ (3) at the
  coefficient universe the extension by zero of Tag 095Z forces.
* `Stacks.EtaleCohomology.isConstructible_of_forall_isConstructibleModuleSheaf` — a complex of
  constructible sheaves of `Λ`-modules represents an object with constructible cohomology
  sheaves. No boundedness is needed.
* `Stacks.EtaleCohomology.isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex`
  — **Tag 0960, the implication (3) ⟹ (1)**.
* `Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum` —
  **Tag 0960, the implication (2) ⟹ (3)**.
* `Stacks.EtaleCohomology.isConstructible_of_isRepresentedByAffineShriekSumComplex` —
  **Tag 0960, the implication (2) ⟹ (1)**.
* `Stacks.EtaleCohomology.exists_affineShriekSum_distTriang_of_isConstructible` — the inductive
  step of the implication (1) ⟹ (2), which is as far as that implication is taken here.

## Implementation notes

Boundedness above of a cochain complex is `CochainComplex.minus` of Tag 013H. "Represented by"
means that the localization functor `DerivedCategory.Q` carries the complex to an object
isomorphic to `K`, as in `Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatComplex`, the
analogous condition (2) of Tag 03TT; that condition asks for a complex which is bounded on both
sides, so it is not the condition (3) of Tag 0960 and a separate definition is needed.

"Flat constructible sheaf of `Λ`-modules" is `AlgebraicGeometry.IsConstructibleFlatModuleSheaf`,
the predicate this development already uses for that phrase in Tag 03TT: local constancy with
finite projective values on the strata of a constructible stratification of every affine open.
No new flatness notion is introduced. `j_{U!} Λ-underline` is
`AlgebraicGeometry.moduleShriekConstant` and constructibility of a sheaf of `Λ`-modules is
`AlgebraicGeometry.IsConstructibleModuleSheaf` of Tag 03RW (3), as in Tag 095Z.

The cohomology sheaves of a complex of constructible sheaves are constructible because the sheaf
of cycles in degree `i` is a kernel of a map between the terms in degrees `i` and `i + 1` and the
cohomology sheaf is a cokernel of a map from the term in degree `i - 1` into it. Neither step
uses a bound on the complex, so the resulting criterion holds for an arbitrary complex; this is
the only place the weak Serre property is used, and it is what makes both (3) ⟹ (1) and
(2) ⟹ (1) work.

### Where the weak Serre property comes from

That the constructible sheaves of `Λ`-modules form a weak Serre subcategory of all sheaves of
`Λ`-modules on the small étale site of `X` — Tag 0754's closure conditions for
`AlgebraicGeometry.isConstructibleModuleSheafProperty` — is Tag 03RZ (3), and it is available:
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`, restated at the
coefficient universe the shriek sums force as
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`. Every statement of this
module at that universe uses it rather than assuming it.

The two statements stated at a coefficient universe `ModuleCat.{w} Λ` with `w` free —
`Stacks.EtaleCohomology.isConstructible_of_forall_isConstructibleModuleSheaf` and
**Tag 0960, the implication (3) ⟹ (1)** — still take the property as the hypothesis `hSerre`,
because Tag 03RZ (3) is proved at `max (u + 1) w` and not below: Tag 093U (3), on which its
proof rests, is stated for a site with objects in `Type c` and morphisms in `Type v` and
coefficients in `ModuleCat.{max c v w} Λ`, so on the small étale site of Tag 021B the ring
universe is not absorbed. Restricting those two statements to `max (u + 1) w` would discharge
the hypothesis, and that instance of them is what the rest of the chapter uses; the free-`w`
form is kept because it is the more general statement.

### Why quasi-separatedness is assumed

Nothing is carried. The one input of the implications proved here which is not the weak Serre
property is that a finite direct sum of sheaves `j_{U!} Λ-underline` with `U` affine is a flat
constructible sheaf of `Λ`-modules. It conjoins two things the source treats as known: Tag 03S8,
that `j_{U!} Λ-underline` is a constructible sheaf, with the flatness of that sheaf, which the
source leaves unstated; and the closure of flat constructible sheaves under finite direct sums.

Both are proved, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek`:
the closure under finite direct sums is
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma`, for an arbitrary ring in an arbitrary
module universe, and the flat refinement of Tag 03S8 is
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant`, whose finite direct sum
form is `AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant`, for a
scheme that is quasi-compact and quasi-separated, at the coefficient ring `Λ : Type r` in a
universe of its own. There is no universe mismatch: the flat refinement no longer passes through
`AlgebraicGeometry.moduleShriekConstantIsoFree` and `ModuleCat.free Λ`, which tied the ring
universe to the module universe, but through `AlgebraicGeometry.moduleShriekConstantIsoCopower`
and `ModuleCat.copower`, which does not, and part (1) of Tag 03S8 is used for a sheaf of sets in
`Type (max (u + 1) r)` as
`AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`.

What the two implications below actually use is the sharper form
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated`,
in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange`, which
asks only that the ambient scheme be quasi-separated, covering it by affine opens and base
changing the extension by zero to each along
`AlgebraicGeometry.moduleShriekConstantSheafPullbackIso`; it is stated at `Λ : Type r` in a
universe of its own, through `AlgebraicGeometry.moduleShriekConstantIsoCopower` for the same
reason. So
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum` and
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByAffineShriekSumComplex` assume `X`
quasi-separated and *not* quasi-compact, which is weaker than the quasi-compact quasi-separated
`X` of the source.

Quasi-separatedness, on the other hand, **cannot** be dropped, and this is why the source
assumes it: a finite affine shriek sum need not be flat constructible on a scheme that is not
quasi-separated. Glue two copies of `Spec k[x_1, x_2, …]` along the complement `V` of the closed
point `(x_1, x_2, …)`, an open subscheme that is not quasi-compact, and let `U` be one of the two
copies — an affine object of the small étale site of the glued scheme `Y`, through an open
immersion. The other copy is an affine open of `Y`, and on it the sheaf `j_{U!} Λ-underline` is
the extension by zero of `Λ-underline` along `V`, so on a stratum of a stratification witnessing
flat constructibility the subset `V` would have to be open and closed; `V` would then be a finite
union of constructible sets, hence constructible, which an open set that is not quasi-compact is
not. So for `Λ ≠ 0` the statement fails at such a `Y`, and a form of it quantified over *every*
scheme of the big étale site would be false rather than merely unproved.

The non-flat Tag 03S8 for sheaves of modules,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, holds at a ring in a universe
of its own as well, by the same copower route; it is the flat refinement with finite projectivity
of the constant values weakened to finite generation. Its quasi-separated-only form is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant_of_quasiSeparated`.

The constructibility statement with no flatness in it — Tag 03S8 together with closure of
constructibility under finite direct sums — at a quasi-compact quasi-separated scheme is
`AlgebraicGeometry.isConstructibleModuleSheaf_sigma_moduleShriekConstant`, Tag 03S8 for sheaves
of modules on each summand assembled by the weak Serre property of Tag 03RZ (3), and that is what
the inductive step below uses. Tag 095Z,
`Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructible_homology`, is
unconditional for the same reason; the covering of an epimorphism onto a constructible sheaf by a
finite direct sum of affine extensions by zero — the conjunction of Tag 093B (2) and Tag 095P
that its proof quotes — is
`AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`.

### Where the converse is proved

The implication (1) ⟹ (2), and with it (1) ⟹ (3) and (3) ⟹ (2), are proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution`, as
`Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_isConstructible`,
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible`
and `Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_constructibleFlat`, and the
equivalence of the three conditions is `Stacks.EtaleCohomology.isConstructible_tfae` there. The
source proves (1) ⟹ (2) by descending induction on `a`, building a complex
`ℱ^a → … → ℱ^b` of finite affine shriek sums together with a map to `K` which is an isomorphism
on cohomology in degrees `> a` and surjective in degree `a`: the base case `a = b` is Tag 095Z,
`Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructible_homology`, and the
inductive step applies Tag 095Z again to the cone of the map constructed so far and then invokes
the octahedral axiom to assemble the extended complex.

That step is `Stacks.EtaleCohomology.exists_affineShriekSum_distTriang_of_isConstructible`: it
produces, from `K` in `D_c` with cohomology vanishing above `b`, a distinguished triangle
`F[-b] ⟶ K ⟶ L ⟶ F[-b][1]` with `F` a finite affine shriek sum whose third vertex is again in
`D_c` and has vanishing cohomology in degrees `≥ b`, which is exactly the input the step needs at
`b - 1`. The module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution` does
not assemble a tower of such triangles: it performs the same descending induction on a cochain
complex representing `K`, which avoids taking a limit of complexes.

## References

* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 095Z](https://stacks.math.columbia.edu/tag/095Z)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 013H](https://stacks.math.columbia.edu/tag/013H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u w v c r

namespace Stacks.Homology

open DerivedCategory CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

variable {C : Type*} [Category C] [Abelian C]

/-- The cohomology of a complex concentrated in degree `b` vanishes in every other degree. -/
public theorem isZero_homologyFunctor_obj_singleFunctor_obj (P : C) (b i : ℤ) (hi : i ≠ b) :
    IsZero ((homologyFunctor C i).obj ((singleFunctor C b).obj P)) :=
  IsZero.of_iso (IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) b P i hi)
    ((homologyFunctorFactors C i).app ((CochainComplex.singleFunctor C b).obj P)))
    ((homologyFunctor C i).mapIso ((singleFunctorIsoCompQ C b).app P))

/-- The degree-`n₀` cohomology of the third vertex of a distinguished triangle vanishes as soon
as the degree-`n₀` cohomology of its second morphism is zero and the degree-`n₀ + 1` cohomology
of its first vertex vanishes: the long exact sequence then exhibits the object as a quotient of
zero. -/
public theorem isZero_homology_obj₃_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hmor₂ : (homologyFunctor C n₀).map T.mor₂ = 0)
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₁)) :
    IsZero ((homologyFunctor C n₀).obj T.obj₃) := by
  have hepi : Epi ((homologyFunctor C n₀).map T.mor₂) :=
    (ShortComplex.exact_iff_epi _ (h₁.eq_of_tgt _ _)).1
      (DerivedCategory.HomologySequence.exact₃ T hT n₀ n₁ h)
  rw [hmor₂] at hepi
  have : Epi (0 : (homologyFunctor C n₀).obj T.obj₂ ⟶ (homologyFunctor C n₀).obj T.obj₃) := hepi
  rw [IsZero.iff_id_eq_zero,
    ← cancel_epi (0 : (homologyFunctor C n₀).obj T.obj₂ ⟶ (homologyFunctor C n₀).obj T.obj₃)]
  simp

/-- A weak Serre subcategory containing the cohomology objects of the first two vertices of a
distinguished triangle contains those of the third: the degree-`n` cohomology of the third
vertex is the middle term of the five term exact sequence
`H^n(T₁) → H^n(T₂) → H^n(T₃) → H^{n+1}(T₁) → H^{n+1}(T₂)` of the triangle. -/
public theorem prop_homology_obj₃_of_distTriang (P : ObjectProperty C) [P.IsWeakSerreClass]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : ∀ i : ℤ, P ((homologyFunctor C i).obj T.obj₁))
    (h₂ : ∀ i : ℤ, P ((homologyFunctor C i).obj T.obj₂)) (n : ℤ) :
    P ((homologyFunctor C n).obj T.obj₃) :=
  ObjectProperty.prop_mid_of_exact₄
    (fun S hS a b c d => P.prop_obj₂_of_exact S hS a b c d)
    (f₀ := (homologyFunctor C n).map T.mor₁) (f₁ := (homologyFunctor C n).map T.mor₂)
    (f₂ := DerivedCategory.HomologySequence.δ T n (n + 1) rfl)
    (f₃ := (homologyFunctor C (n + 1)).map T.mor₁)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])
    (DerivedCategory.HomologySequence.comp_δ T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.δ_comp T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.exact₂ T hT n)
    (DerivedCategory.HomologySequence.exact₃ T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.exact₁ T hT n (n + 1) rfl)
    (h₁ n) (h₂ n) (h₁ (n + 1)) (h₂ (n + 1))

end Stacks.Homology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]

/-- **Stacks 03RZ (3) in the form the complexes of this chapter ask for.** For `Λ` a Noetherian
ring, constructibility of a sheaf of `Λ`-modules on the small étale site of `X` — as a property
of objects of the abelian category of all such sheaves, `isConstructibleModuleSheafProperty` —
is a weak Serre class in the sense of Tag 0754: it contains the zero object, is closed under
isomorphism, and is closed under kernels, cokernels and extensions.

This is `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` read through
the definitional unfolding of `AlgebraicGeometry.isConstructibleModuleSheafProperty`. The
coefficient universe is `max (u + 1) w` there and `max (u + 1) r` here, the one the extension by
zero of Tag 095Z forces; it is the instantiation `w := r` of that theorem. No hypothesis on `X`
enters. -/
public theorem isWeakSerreClass_isConstructibleModuleSheafProperty :
    (isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r} B X Λ

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section General

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]

/-- **Condition (3) of Tag 0960.** An object of the unbounded derived category of small-étale
sheaves of `Λ`-modules is represented by a bounded above complex of flat constructible sheaves
of `Λ`-modules.

This is not the condition (2) of Tag 03TT,
`Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatComplex`, which asks for a complex
bounded on both sides. -/
public def IsRepresentedByBoundedAboveConstructibleFlatComplex
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) : Prop :=
  ∃ L : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ,
    CochainComplex.minus _ L ∧ (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (L.X i)) ∧
      Nonempty (DerivedCategory.Q.obj L ≅ K)

omit [IsNoetherianRing Λ] in
/-- An object of `D(X_étale, Λ)` represented by a complex of constructible sheaves of
`Λ`-modules has constructible cohomology sheaves, so it lies in the constructible derived
category of Tag 095W.

The cohomology sheaf in degree `i` is a cokernel of a map from the term in degree `i - 1` into
the sheaf of cycles, which is a kernel of a map between the terms in degrees `i` and `i + 1`;
each term is constructible, and the hypothesis `hSerre` that the constructible sheaves of
`Λ`-modules form a weak Serre subcategory of all sheaves of `Λ`-modules — Tag 0754, closure
under kernels, cokernels, extensions and isomorphism — carries constructibility to the kernel
and then to the cokernel. The complex is not assumed bounded in either direction. -/
public theorem isConstructible_of_forall_isConstructibleModuleSheaf
    (hSerre : (isConstructibleModuleSheafProperty.{u, w, r} B X Λ).IsWeakSerreClass)
    (L : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hL : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (L.X i))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (e : DerivedCategory.Q.obj L ≅ K) :
    IsConstructible B X Λ K := by
  have := hSerre
  set P := isConstructibleModuleSheafProperty.{u, w, r} B X Λ
  intro i
  have hcycles : P (L.cycles i) :=
    P.prop_of_isLimit_kernelFork (L.cyclesIsKernel i (i + 1) (by simp)) (hL i) (hL (i + 1))
  have hhomology : P (L.homology i) :=
    P.prop_of_isColimit_cokernelCofork (L.homologyIsCokernel (i - 1) i (by simp))
      (hL (i - 1)) hcycles
  exact P.prop_of_iso
    (((DerivedCategory.homologyFunctorFactors
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) i).app L).symm ≪≫
      (DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) i).mapIso e)
    hhomology

omit [IsNoetherianRing Λ] in
/-- **Tag 0960, the implication (3) ⟹ (1).** An object of `D(X_étale, Λ)` represented by a
bounded above complex of flat constructible sheaves of `Λ`-modules has constructible cohomology
sheaves.

A flat constructible sheaf is constructible, by
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`, and a complex
of constructible sheaves has constructible cohomology, by
`Stacks.EtaleCohomology.isConstructible_of_forall_isConstructibleModuleSheaf`, which is where
the weak Serre hypothesis `hSerre` is used; see "Where the weak Serre property comes from" in the
module documentation for why it is still a hypothesis at a free coefficient universe, and
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty` for what discharges it
at `max (u + 1) r`. The bound is not needed for this implication and is not used. -/
@[stacks 0960 "the implication (3) => (1), from the weak Serre property `hSerre` of the \
constructible sheaves of modules"]
public theorem isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex
    (hSerre : (isConstructibleModuleSheafProperty.{u, w, r} B X Λ).IsWeakSerreClass)
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (hK : IsRepresentedByBoundedAboveConstructibleFlatComplex.{u, w, r} B X Λ K) :
    IsConstructible B X Λ K := by
  obtain ⟨L, -, hterm, ⟨e⟩⟩ := hK
  exact isConstructible_of_forall_isConstructibleModuleSheaf B X Λ hSerre L
    (fun i => isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hterm i)) K e

end General

section Shriek

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]

/-- **Condition (2) of Tag 0960.** An object of the unbounded derived category of small-étale
sheaves of `Λ`-modules is represented by a bounded above complex each of whose terms is a finite
direct sum of sheaves `j_{U!} Λ-underline` with `U` an affine object of the small étale site of
`X`.

The coefficient universe is the one extension by zero forces, as in Tag 095Z. -/
public def IsRepresentedByAffineShriekSumComplex
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) : Prop :=
  ∃ L : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) ℤ,
    CochainComplex.minus _ L ∧
      (∀ i : ℤ, ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
        (∀ j, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j))) ∧
          Nonempty (L.X i ≅ ∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j))) ∧
      Nonempty (DerivedCategory.Q.obj L ≅ K)

omit [IsNoetherianRing Λ] in
/-- **Tag 0960, the implication (2) ⟹ (3).** A bounded above complex whose terms are finite
direct sums of sheaves `j_{U!} Λ-underline` with `U` affine is a bounded above complex of flat
constructible sheaves of `Λ`-modules, so an object of `D(X_étale, Λ)` satisfying condition (2)
satisfies condition (3).

The same complex is used; each term is isomorphic to a finite direct sum of affine shriek
constants, which is flat constructible by
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated`,
and flat constructibility is invariant under isomorphism by
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_congr`. That input conjoins Tag 03S8 with the
flatness of `j_{U!} Λ-underline`, which the source leaves unstated, and the closure of flat
constructible sheaves under finite direct sums; see "Why quasi-separatedness is assumed" in the
module documentation for why it is the only hypothesis on `X` that enters. Quasi-compactness of
`X` is not needed for this implication and is not assumed. -/
@[stacks 0960 "the implication (2) => (3)"]
public theorem isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum
    [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByAffineShriekSumComplex.{u, r} B X Λ K) :
    IsRepresentedByBoundedAboveConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K := by
  obtain ⟨L, hminus, hterm, ⟨e⟩⟩ := hK
  refine ⟨L, hminus, fun i => ?_, ⟨e⟩⟩
  obtain ⟨n, U, hU, ⟨eU⟩⟩ := hterm i
  exact isConstructibleFlatModuleSheaf_congr B X Λ eU.symm
    (isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated B X Λ U hU)

/-- **Tag 0960, the implication (2) ⟹ (1).** An object of `D(X_étale, Λ)` represented by a
bounded above complex whose terms are finite direct sums of sheaves `j_{U!} Λ-underline` with
`U` affine has constructible cohomology sheaves, so it lies in the constructible derived
category of Tag 095W.

This is the composite of the implications (2) ⟹ (3) and (3) ⟹ (1), and nothing is carried. The
weak Serre property the second step needs is at this coefficient universe Stacks 03RZ (3),
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`; the flat
constructibility of a finite affine shriek sum which the first step needs is
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated`,
and that is the only reason `X` is asked to be quasi-separated. Quasi-compactness of `X` is not
needed and is not assumed. -/
@[stacks 0960 "the implication (2) => (1)"]
public theorem isConstructible_of_isRepresentedByAffineShriekSumComplex
    [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByAffineShriekSumComplex.{u, r} B X Λ K) :
    IsConstructible B X Λ K :=
  isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex B X Λ
    (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K
    (isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum B X Λ K hK)

/-- **The inductive step of the implication (1) ⟹ (2) of Tag 0960.** Let `K` lie in
`D_c(X_étale, Λ)` and let `b` be an integer above which the cohomology of `K` vanishes. Then
there are finitely many affine objects `U i` of the small étale site of `X` and a distinguished
triangle `F[-b] ⟶ K ⟶ L ⟶ F[-b][1]`, with `F = ⊕ᵢ j_{U i!} Λ-underline`, whose third vertex `L`
again lies in `D_c(X_étale, Λ)` and has vanishing cohomology in every degree `≥ b`.

This is the step the source iterates in the descending induction proving (1) ⟹ (2): the map
`F[-b] ⟶ K` is produced by Tag 095Z,
`Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructible_homology`, and the
cone on it is the object to which Tag 095Z is applied next. Assembling the sequence of such
steps into a single bounded above complex of shriek sums is done in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution`, by the
same induction carried out on a cochain complex representing `K`.

The vanishing of `H^i(L)` for `i ≥ b` comes from
`Stacks.Homology.isZero_homology_obj₃_of_distTriang`: in degree `b` because `H^b(F[-b]) ⟶ H^b(K)`
is surjective, and in degree `i > b` because `H^i(K)` already vanishes; in both cases
`H^{i+1}(F[-b])` vanishes because `i + 1 ≠ b`. Constructibility of the cohomology of `L` comes
from `Stacks.Homology.prop_homology_obj₃_of_distTriang` and the weak Serre property of the
constructible sheaves of `Λ`-modules, Stacks 03RZ (3), which at this coefficient universe is
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty` and is not carried.

Constructibility of the shriek sum `F` itself, which the weak Serre argument needs in degree `b`,
is `AlgebraicGeometry.isConstructibleModuleSheaf_sigma_moduleShriekConstant`: Tag 03S8 for
sheaves of modules on each summand, assembled by the same weak Serre property. Nothing is
carried. -/
public theorem exists_affineShriekSum_distTriang_of_isConstructible
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (hK : IsConstructible B X Λ K) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) i).obj K)) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ j, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j))) ∧
      ∃ (L : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)))
        (f : (DerivedCategory.singleFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) b).obj
            (∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j)) ⟶ K) (g : K ⟶ L)
        (h : L ⟶ ((DerivedCategory.singleFunctor
          (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) r} Λ)) b).obj
              (∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j)))⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧ IsConstructible B X Λ L ∧
          ∀ i : ℤ, b ≤ i → IsZero ((DerivedCategory.homologyFunctor
            (Sheaf (SmallEtale.topology B X.obj X.property)
              (ModuleCat.{max (u + 1) r} Λ)) i).obj L) := by
  obtain ⟨n, U, hU, f, hf⟩ :=
    exists_shriekConstant_cover_of_isConstructible_homology B Λ X K b (hK b)
  obtain ⟨L, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have := isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ
  set P := isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ with hP
  have hsingle : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ b).obj
        (∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j)))) := by
    intro i
    by_cases hi : i = b
    · subst hi
      exact P.prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app _).symm
        (isConstructibleModuleSheaf_sigma_moduleShriekConstant B X Λ U hU)
    · exact P.prop_of_isZero
        (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b i hi)
  refine ⟨n, U, hU, L, f, g, h, hT, fun i => ?_, fun i hi => ?_⟩
  · exact Stacks.Homology.prop_homology_obj₃_of_distTriang P _ hT hsingle hK i
  · refine Stacks.Homology.isZero_homology_obj₃_of_distTriang _ hT i (i + 1) rfl ?_
      (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b (i + 1) (by omega))
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT b).1 hf
    · exact (hvan i hlt).eq_of_src _ _

end Shriek

end Stacks.EtaleCohomology

end
