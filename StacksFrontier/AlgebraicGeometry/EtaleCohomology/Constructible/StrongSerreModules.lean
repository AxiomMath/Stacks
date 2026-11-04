module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocallyConstantSubsheafConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerre

/-!
# Constructible sheaves of modules form a strong Serre subcategory

Let `X` be a Noetherian scheme and let `Λ` be a Noetherian ring. The constructible sheaves of
`Λ`-modules on the small étale site of `X` are closed under subobjects and under quotients, and
together with the weak Serre property of Stacks 03RZ (3) that makes them a strong Serre
subcategory of all sheaves of `Λ`-modules. This is part (3) of Stacks 09BH.

The route of parts (1) and (2) does not reach part (3). For sheaves of sets a subobject of a
representable sheaf is representable, and for sheaves of abelian groups constructibility is a
property of the underlying sheaf of sets; a sheaf of `Λ`-modules has neither feature, because
local constancy of finite type bounds the constant values only up to finite generation and a
finitely generated module over a Noetherian ring carries no finiteness on its underlying set.
So the source's own route is taken here. Its geometric step — a subsheaf of a sheaf of
`Λ`-modules which is locally constant of finite type on all of an immersed subscheme of `X` is
constructible there — is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_mono_of_isFiniteTypeLocallyConstant`, and
`AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible` below records it in the
shape the rest of this file uses.

That step is what reduces part (3) to a single stratification. A constructible sheaf admits
**one** stratification of the whole scheme, by Stacks 095E, on each stratum of which it is
locally constant of finite type; inverse image to a stratum is left exact, so it carries a
subsheaf to a subsheaf, and the geometric step makes the restricted subsheaf constructible on
that stratum; the strata are immersed with constructible images and cover `X`, so Stacks 09YR
assembles those restrictions into constructibility on `X`. Quotients then follow from
subobjects, an epimorphism being the cokernel of its kernel, and the strong Serre property
follows from both.

## Main definitions

* `AlgebraicGeometry.FiniteTypeLocallyConstantSubsheavesAreConstructible` — the geometric step of
  the source's proof, as a proposition about `X`.

## Main results

* `AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible` — that proposition,
  proved.
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_mono` — **Stacks 09BH (3), subsheaves.**
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_epi` — **Stacks 09BH (3), quotient sheaves.**
* `AlgebraicGeometry.isConstructibleModuleSheaf_forall_epi` — the same statement quantified over
  the epimorphism, which is the form Stacks 0F0N (2) consumes.
* `AlgebraicGeometry.isSerreClass_isConstructibleModuleSheaf` — **Stacks 09BH (3), the strong
  Serre property.**

## Implementation notes

The geometric step is the case of part (3) in which the ambient sheaf is locally constant of
finite type on the whole of an immersed subscheme of `X`, so that no stratification of it is
involved. It is a Noetherian induction on that subscheme: at an irreducible piece one passes to
an étale neighbourhood on which the ambient sheaf is constant and reads the subsheaf off there,
which makes the subsheaf constant on a further neighbourhood, and that neighbourhood is étale
and surjective over an open subscheme of the piece.

**No descent along `U ×_X U ⇉ U` occurs at that step.** What is wanted of the stratum is *local
constancy*, which is a statement about some étale covering of it; the neighbourhood is itself
such a covering of the open part of the stratum it dominates, so the sections of the subsheaf
over it are used as they stand and nothing has to be descended to the stratum. Its three
geometric inputs are
`AlgebraicGeometry.SmallEtale.bijective_toSheafify_const_app_of_irreducibleSpace` (the sections
of a constant sheaf of modules over an irreducible object of the small étale site are the
constants), `AlgebraicGeometry.exists_constantSheafIso_overPullback_of_mono` (a subsheaf of a
constant sheaf of modules is constant on an étale neighbourhood, by a maximality argument that
needs no geometric point at all) and
`AlgebraicGeometry.exists_irreducible_trivializing_object` (the trivialising neighbourhood can
be taken irreducible); the induction itself is
`AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace`. Stacks 095E, Stacks 09YR
and Stacks 03RZ (3) are all discharged from the library too, so every statement below is
unconditional.

The proposition is stated for the subschemes immersed in `X` rather than for an arbitrary
scheme, because those are the only ones it is applied to and because it is for those that the
Noetherian hypothesis of Stacks 09BH is automatic.

The coefficient universe is `ModuleCat.{u + 1} Λ` with `Λ : Type (u + 1)`, the one at which
Stacks 03RZ (3) is available on this site and the one Stacks 0F0N uses. The universe arguments of
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` and of
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat` are written out:
both are stated with a coefficient universe of the form `max (u + 1) w`, and instance search
cannot solve such a `max` against `u + 1`.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]

/-- **The geometric step of Stacks 09BH (3).** A subsheaf of a sheaf of `Λ`-modules which is
locally constant of finite type on the whole of a subscheme immersed in `X` is constructible on
that subscheme.

This is the case of Stacks 09BH (3) in which the ambient sheaf needs no stratification, and it is
the one step of the source's proof that is geometric rather than categorical: one passes to an
étale neighbourhood of the generic point of an irreducible piece, where the ambient sheaf is
constant, and reads the subsheaf off there. That neighbourhood is itself an étale covering of the
open part of the piece it dominates, so **nothing is descended along `U ×_X U ⇉ U`**. It is proved
in `AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible`. -/
public def FiniteTypeLocallyConstantSubsheavesAreConstructible : Prop :=
  ∀ (Z : B.Scheme) (g : Z ⟶ X), IsImmersion (B.inclusion.map g) →
    ∀ (G F : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)) (i : G ⟶ F),
      Mono i →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B Z.obj Z.property) F →
      IsConstructibleModuleSheaf B Z Λ G

/-- **The geometric step of Stacks 09BH (3) holds.** A subscheme immersed in a Noetherian scheme
has Noetherian underlying space and is locally Noetherian — an immersion is a topological
embedding and is locally of finite type — so
`AlgebraicGeometry.isConstructibleModuleSheaf_of_mono_of_isFiniteTypeLocallyConstant` applies to
it.

No `@[stacks]` attribute appears on this statement: it is a step of the proof of Stacks 09BH (3),
and the tag is attributed to the statements of that part below. -/
public theorem finiteTypeLocallyConstantSubsheavesAreConstructible [IsNoetherian X.obj] :
    FiniteTypeLocallyConstantSubsheavesAreConstructible B X Λ := by
  intro Z g hg G F i hi hF
  have hNoeth := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have hlnX : IsLocallyNoetherian (B.inclusion.obj X) := hNoeth.1
  have hnsX : TopologicalSpace.NoetherianSpace (B.inclusion.obj X) :=
    (inferInstance : TopologicalSpace.NoetherianSpace X.obj)
  have hlnZ : IsLocallyNoetherian Z.obj :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map g)
  have hnsZ : TopologicalSpace.NoetherianSpace Z.obj :=
    (B.inclusion.map g).isEmbedding.isInducing.noetherianSpace
  exact isConstructibleModuleSheaf_of_mono_of_isFiniteTypeLocallyConstant B Λ Z i hF

/-- **Stacks 09BH, part (3), subsheaves.** A subsheaf of a constructible sheaf of `Λ`-modules on
the small étale site of a Noetherian scheme is constructible.

By Stacks 095E the ambient sheaf is locally constant of finite type on the strata of a single
stratification of `X`. Inverse image to a stratum is left exact, so the subsheaf restricts to a
subsheaf there, and the geometric step of the source's proof,
`AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible`, makes that restriction
constructible on the stratum. The strata are immersed with constructible images and they cover
`X`, so Stacks 09YR carries constructibility back to `X`. -/
@[stacks 09BH "part (3), subsheaf; Stacks 095E, Stacks 09YR, Stacks 03RZ (3) and the geometric \
step of the source's proof are all discharged from the library"]
public theorem isConstructibleModuleSheaf_of_mono [IsNoetherian X.obj]
    {G F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructibleModuleSheaf B X Λ G := by
  have hNoeth := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have _ : CompactSpace X.obj := hNoeth.2
  have _ : IsLocallyNoetherian X.obj := hNoeth.1
  have _ : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨s, hs⟩ := (isConstructibleModuleSheaf_iff_exists_stratification B X Λ F).1 hF
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B X Λ G
    s.piece s.inclusion s.isImmersion
    (fun k => isConstructible_range_of_isConstructible_top B X (s.inclusion k)
      (s.constructible k))
    (by simpa using s.covers) (fun k => ?_)
  let pull := (smallEtaleBaseChange B (s.inclusion k)).sheafPullback (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (s.piece k).obj (s.piece k).property)
  have _ : PreservesFiniteLimits pull :=
    preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B
      (s.inclusion k) Λ
  exact finiteTypeLocallyConstantSubsheavesAreConstructible B X Λ (s.piece k) (s.inclusion k)
    (s.isImmersion k) _ _ (pull.map i) (preserves_mono_of_preservesLimit pull i) (hs k)

/-- **Closure under subobjects**, as a property of the class of constructible sheaves of
`Λ`-modules; this is `AlgebraicGeometry.isConstructibleModuleSheaf_of_mono` in the form the
categorical reductions consume. -/
public theorem isClosedUnderSubobjects_isConstructibleModuleSheaf [IsNoetherian X.obj]
    (hloc : FiniteTypeLocallyConstantSubsheavesAreConstructible B X Λ) :
    ObjectProperty.IsClosedUnderSubobjects
      (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) =>
        IsConstructibleModuleSheaf B X Λ F) := by
  have := hloc
  exact ⟨fun i _ hF => isConstructibleModuleSheaf_of_mono B X Λ i hF⟩

/-- **Stacks 09BH, part (3), quotient sheaves.** A quotient of a constructible sheaf of
`Λ`-modules on the small étale site of a Noetherian scheme is constructible.

An epimorphism of sheaves of modules is the cokernel of its kernel; the kernel is a subobject, so
it is constructible by `AlgebraicGeometry.isConstructibleModuleSheaf_of_mono`, and the weak Serre
property of Stacks 03RZ (3) then puts the target in the class. -/
@[stacks 09BH "part (3), quotient sheaf; Stacks 095E, Stacks 09YR, Stacks 03RZ (3) and the \
geometric step of the source's proof are all discharged from the library"]
public theorem isConstructibleModuleSheaf_of_epi [IsNoetherian X.obj]
    {G Q : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (p : G ⟶ Q) [Epi p] (hG : IsConstructibleModuleSheaf B X Λ G) :
    IsConstructibleModuleSheaf B X Λ Q := by
  let P : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{u + 1} Λ)) := fun F => IsConstructibleModuleSheaf B X Λ F
  have _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X Λ
  have _ : P.IsClosedUnderSubobjects :=
    isClosedUnderSubobjects_isConstructibleModuleSheaf B X Λ
      (finiteTypeLocallyConstantSubsheavesAreConstructible B X Λ)
  have := P.isClosedUnderQuotients_of_isClosedUnderSubobjects
  exact P.prop_of_epi p hG

/-- **Stacks 09BH, part (3), quotient sheaves**, as a single proposition quantified over the
epimorphism. This is the form Stacks 0F0N (2) consumes, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SpecializationClosedSupportColimit`,
where it is needed to see that the image of a map out of a constructible sheaf of `Λ`-modules is
constructible. Quantifying over the epimorphism is what lets part (2) apply it once. -/
public theorem isConstructibleModuleSheaf_forall_epi [IsNoetherian X.obj]
    (_hloc : FiniteTypeLocallyConstantSubsheavesAreConstructible B X Λ) :
    ∀ (G Q : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) (p : G ⟶ Q),
      Epi p → IsConstructibleModuleSheaf B X Λ G → IsConstructibleModuleSheaf B X Λ Q :=
  fun _ _ p _ hG => isConstructibleModuleSheaf_of_epi B X Λ p hG

/-- **Stacks 09BH, part (3).** The constructible sheaves of `Λ`-modules on the small étale site
of a Noetherian scheme form a *strong* Serre subcategory of all sheaves of `Λ`-modules on that
site: `CategoryTheory.ObjectProperty.IsSerreClass` is closure under subobjects, quotients and
extensions together with containing zero, which is the characterisation of a Serre subcategory in
Stacks 02MP.

Closure under extensions and the zero object are the weak Serre property of Stacks 03RZ (3),
which is unconditional; closure under subobjects is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_mono`, and it implies closure under quotients
because an epimorphism is the cokernel of its kernel. -/
@[stacks 09BH "part (3), the strong Serre property; Stacks 095E, Stacks 09YR, Stacks 03RZ (3) \
and the geometric step of the source's proof are all discharged from the library"]
public theorem isSerreClass_isConstructibleModuleSheaf [IsNoetherian X.obj] :
    ObjectProperty.IsSerreClass
      (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) =>
        IsConstructibleModuleSheaf B X Λ F) := by
  let P : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{u + 1} Λ)) := fun F => IsConstructibleModuleSheaf B X Λ F
  have _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X Λ
  have _ : P.IsClosedUnderSubobjects :=
    isClosedUnderSubobjects_isConstructibleModuleSheaf B X Λ
      (finiteTypeLocallyConstantSubsheavesAreConstructible B X Λ)
  exact P.isSerreClass_of_isClosedUnderSubobjects

end AlgebraicGeometry

end
