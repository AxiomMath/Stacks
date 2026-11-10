module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# A finite shriek presentation makes a module sheaf finitely presentable

Stacks 095N presents a constructible sheaf of modules over a Noetherian ring on a quasi-compact
quasi-separated scheme as the cokernel of a map between finite direct sums of extensions by zero
of constant free rank-one module sheaves, and Stacks 09Z4 concludes from such a presentation that
the sheaf is a compact — that is, finitely presentable — object of the category of sheaves of
modules. This file proves that implication for the presentation predicate the library actually
has, `AlgebraicGeometry.HasFiniteShriekPresentation`.

The generators of such a presentation are `AlgebraicGeometry.moduleShriekConstant`, built as the
sheaf pullback along `AlgebraicGeometry.smallEtalePostcompose` of a constant sheaf, whereas
`CategoryTheory.Sheaf.isFinitelyPresentable_coequalizer_sigma_composeAndSheafify_free` asserts
finite presentability for the *free module sheaf on a sheafified representable*. Those are the
same sheaf, and identifying them would mean comparing two left adjoints. That comparison is not
made here, and is not needed: the extension by zero of a constant sheaf is itself a value of a
composite left adjoint, so its finite presentability follows from the same two facts directly —
that the right adjoint of that composite is sections over the étale object, and that sections over
an object with a cofinal system of finite coverings with quasi-compact fibre products commute with
filtered colimits of module sheaves (part (4) of Stacks 0738, proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves`). The
free-module functor, and hence the tie of the ring universe to the module universe that it carries,
does not enter.

## Main results

* `ModuleCat.coyonedaULiftSelfIso` and `ModuleCat.isFinitelyPresentable_uliftSelf` — maps out of
  the free rank-one module are its elements, so it is a finitely presentable module.
* `CategoryTheory.Sheaf.isFinitelyPresentable_sheafPullback_constantSheaf` — for a continuous
  functor of sites out of a site with a terminal object, the sheaf pullback of a constant sheaf at
  a finitely presentable object is finitely presentable, as soon as sections over the image of the
  terminal object commute with filtered colimits.
* `CategoryTheory.Sheaf.exists_isFinitelyPresentable_sheafPullback_constantSheaf_bot` — the
  hypotheses of that statement are satisfiable.
* `AlgebraicGeometry.isFinitelyPresentable_moduleShriekConstant` — the extension by zero of the
  constant free rank-one module sheaf from an étale object with a cofinal system of finite
  coverings with quasi-compact fibre products is finitely presentable.
* `AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation` — hence so is any sheaf
  of modules carrying a finite shriek presentation by such objects. This is the half of the module
  case of **Stacks 09Z4** that remains once Stacks 095N has produced the presentation.
* `AlgebraicGeometry.exists_hasFiniteShriekPresentation` and
  `AlgebraicGeometry.exists_isFinitelyPresentable_moduleSheaf` — the presentation predicate is
  inhabited and the conclusion of the previous statement is reached.

## Implementation notes

The universes of the two geometric statements are pinned, and the pin is forced rather than
chosen. For `B : BigEtaleSite.{u}` the small étale site is a `Type (u + 1)` with
`Category.{u}`, so the sheaves-of-sets form of part (4) of Stacks 0738 — and with it its
module-valued form — is available only at the coefficient universe `u + 1`. The module universe of
`AlgebraicGeometry.moduleShriekConstant` is `max (u + 1) r w` for a ring in `Type r` and a
presented sheaf in `ModuleCat.{w}`, so the two agree exactly when `r` and `w` are at most `u + 1`,
which is written here as `r = w = u + 1`. A ring in a smaller universe can be replaced by an
isomorphic one in `Type (u + 1)`, but that is a different ring object, so the statements below are
about `R : Type (u + 1)` and nothing weaker is claimed.

`AlgebraicGeometry.HasFiniteShriekPresentation` identifies the underlying presheaf of the cokernel
with the pointwise universe lift of the presented sheaf rather than with the sheaf itself, which is
what lets its module universe be independent of the site and the ring. At `w = u + 1` that lift is
a lift inside one universe, so `ModuleCat.uliftFunctorSelfIso` turns the identification into an
isomorphism of sheaves.

Neither geometric statement carries a Stacks tag: Stacks 095N is the production of the
presentation, which is not proved here, and the covering hypothesis on the étale objects is carried
explicitly rather than derived from quasi-compactness and quasi-separatedness of the schemes, which
is `AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`. Note also that nothing in the
library constructs a `AlgebraicGeometry.BigEtaleSite`, so every statement about one is conditional
on an unexhibited structure;
`CategoryTheory.Sheaf.exists_isFinitelyPresentable_sheafPullback_constantSheaf_bot`
discharges the whole chain on a site that does exist.

`Fact Cardinal.aleph0.IsRegular` is a local instance, as in Mathlib's file on finitely presentable
objects, and the two coproduct instances are given the priority they have in
`AlgebraicGeometry.HasFiniteShriekPresentation`'s own file so that the direct sums match.

## References

* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t vA uA v u v' u' r s

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace ModuleCat

/-- **Maps out of the free rank-one module are its elements.** The isomorphism of functors sending
a linear map to the image of the generator; its inverse sends an element to the linear map it
spans. The rank-one module is written as a universe lift of the ring, so that the module universe
may be larger than the ring universe. -/
public def coyonedaULiftSelfIso (R : Type r) [Ring R] :
    coyoneda.obj (op (ModuleCat.of R (ULift.{s} R))) ≅ forget (ModuleCat.{max r s} R) :=
  NatIso.ofComponents
    (fun M => Equiv.toIso
      { toFun := fun f => f.hom (ULift.up 1)
        invFun := fun m => ModuleCat.ofHom
          ((LinearMap.toSpanSingleton R M m).comp (ULift.moduleEquiv).toLinearMap)
        left_inv := by
          intro f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change x.down • f.hom (ULift.up 1) = f.hom x
          rw [← map_smul]
          congr 1
          apply ULift.ext
          simp
        right_inv := by intro m; simp })
    (fun g => by ext f; show _ = _; rfl)

/-- **The free rank-one module is a finitely presentable object.** Maps out of it are its elements
by `ModuleCat.coyonedaULiftSelfIso`, and the forgetful functor commutes with filtered colimits —
which, since the standard instance ties the module universe to the ring universe, is routed through
abelian groups. -/
public theorem isFinitelyPresentable_uliftSelf (R : Type r) [Ring R] :
    IsFinitelyPresentable.{max r s} (ModuleCat.of R (ULift.{s} R)) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  let : PreservesColimitsOfSize.{max r s, max r s}
      (forget₂ (ModuleCat.{max r s} R) AddCommGrpCat.{max r s}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max r s, r, max r s, max r s} R
  let : PreservesFilteredColimits (forget (ModuleCat.{max r s} R)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max r s} R) AddCommGrpCat.{max r s}) (forget AddCommGrpCat.{max r s})
  refine ⟨fun {I} _ _ => ⟨fun {F} => ?_⟩⟩
  exact preservesColimit_of_natIso _ (coyonedaULiftSelfIso.{r, s} R).symm

/-- **Lifting modules into their own universe is the identity**, up to the isomorphism given
componentwise by `ULift.moduleEquiv`. -/
public def uliftFunctorSelfIso (R : Type r) [Ring R] :
    ModuleCat.uliftFunctor.{s, s, r} R ≅ 𝟭 (ModuleCat.{s} R) :=
  NatIso.ofComponents
    (fun M => LinearEquiv.toModuleIso (ULift.moduleEquiv (R := R) (M := M)))
    (fun f => by ext x; rfl)

end ModuleCat

namespace CategoryTheory.Sheaf

/-- **Extension by zero of a constant sheaf preserves finite presentability.** Let `π` be a
continuous functor from a site with a terminal object `T` to another site. The sheaf pullback along
`π` of the constant sheaf at a finitely presentable object is finitely presentable, provided
sections over `π.obj T` commute with filtered colimits.

The sheaf pullback is left adjoint to the direct image and the constant sheaf functor is left
adjoint to sections over `T`, so the composite is a left adjoint whose right adjoint is sections
over `π.obj T`; a left adjoint whose right adjoint commutes with filtered colimits preserves
finitely presentable objects. -/
public theorem isFinitelyPresentable_sheafPullback_constantSheaf
    {C' : Type u'} [Category.{v'} C'] {C : Type u} [Category.{v} C]
    (π : C' ⥤ C) (JC' : GrothendieckTopology C') (JC : GrothendieckTopology C)
    [π.IsContinuous JC' JC]
    (A : Type uA) [Category.{vA} A] [HasWeakSheafify JC' A] [HasWeakSheafify JC A]
    [∀ (F : C'ᵒᵖ ⥤ A), π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) (M : A) [IsFinitelyPresentable.{t} M]
    (hS : PreservesFilteredColimitsOfSize.{t, t} ((sheafSections JC A).obj (op (π.obj T)))) :
    IsFinitelyPresentable.{t} ((Functor.sheafPullbackConstruction.sheafPullback π A JC' JC).obj
      ((constantSheaf JC' A).obj M)) := by
  have adj := (constantSheafAdj JC' A hT).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous π A JC' JC)
  let hiso : (sheafSections JC A).obj (op (π.obj T)) ≅
      (π.sheafPushforwardContinuous A JC' JC) ⋙ (sheafSections JC' A).obj (op T) :=
    Iso.refl _
  let : ((sheafSections JC A).obj (op (π.obj T))).IsFinitelyAccessible.{t} :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.2 hS
  let : ((π.sheafPushforwardContinuous A JC' JC) ⋙
      (sheafSections JC' A).obj (op T)).IsCardinalAccessible (Cardinal.aleph0.{t}) :=
    Functor.isCardinalAccessible_of_natIso hiso _
  exact adj.isCardinalPresentable_leftAdjoint_obj _ M

/-- **The hypotheses above are satisfiable.** On the trivial topology, with `π` the identity
functor, every object has the covering property of part (4) of Stacks 0738
(`CategoryTheory.GrothendieckTopology.hasFiniteQuasiCompactCoverings_bot`), module-valued
presheaves admit weak sheafification, and the free rank-one module is finitely presentable, so the
whole chain is dischargeable and no statement above is conditional on an unexhibited
hypothesis. -/
public theorem exists_isFinitelyPresentable_sheafPullback_constantSheaf_bot {C : Type u}
    [Category.{v} C] {T : C} (hT : IsTerminal T) (R : Type max u v) [Ring R] :
    ∃ G : Sheaf (⊥ : GrothendieckTopology C) (ModuleCat.{max u v} R),
      IsFinitelyPresentable.{max u v} G := by
  let := hasWeakSheafify_moduleCat.{max u v, v, u} (⊥ : GrothendieckTopology C) R
  let := ModuleCat.isFinitelyPresentable_uliftSelf.{max u v, max u v} R
  refine ⟨_, isFinitelyPresentable_sheafPullback_constantSheaf (𝟭 C) ⊥ ⊥
    (ModuleCat.{max u v} R) hT (ModuleCat.of R (ULift.{max u v} R)) ?_⟩
  exact preservesFilteredColimitsOfSize_sheafSections_moduleCat.{max u v, v, u} ⊥ R
    (GrothendieckTopology.hasFiniteQuasiCompactCoverings_bot T)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

/-- **Composition with `U ⟶ X` carries the terminal object of the small étale site of `U` to
`U`.** The terminal object is `U` with its identity structure morphism, and composing that identity
with `U ⟶ X` gives `U` again. -/
public def smallEtalePostcomposeFinalIso (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.1 X.property) :
    (smallEtalePostcompose B X.1 X.property U).obj
      (SmallEtale.final B U.obj.left.1 U.obj.left.property) ≅ U :=
  (BigEtaleOver.IsEtaleOver B X.1 X.property).fullyFaithfulι.preimageIso
    (Over.isoMk (Iso.refl _) rfl)

/-- **The extension by zero of the constant free rank-one module sheaf is finitely
presentable**, for an étale object `U` of `X` all of whose coverings are refined by finite
coverings with quasi-compact fibre products.

This is the generator of the presentations of Stacks 095N, and the point at which part (4) of
Stacks 0738 for sheaves of modules enters the module case of Stacks 09Z4: the right adjoint of the
composite left adjoint producing `AlgebraicGeometry.moduleShriekConstant` is sections over `U`, and
those commute with filtered colimits. -/
public theorem isFinitelyPresentable_moduleShriekConstant (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type (u + 1)) [CommRing R] (U : SmallEtale B X.1 X.property)
    (H : (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings U) :
    IsFinitelyPresentable.{u + 1} (moduleShriekConstant.{u, u + 1, u + 1} B X R U) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left R
  let := ModuleCat.isFinitelyPresentable_uliftSelf.{u + 1, u + 1} R
  refine Sheaf.isFinitelyPresentable_sheafPullback_constantSheaf
    (smallEtalePostcompose B X.1 X.property U) _ _ _
    (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property) _ ?_
  have h := Sheaf.preservesFilteredColimitsOfSize_sheafSections_moduleCat.{u + 1, u, u + 1}
    (SmallEtale.topology B X.1 X.property) R H
  refine ⟨fun {I} _ _ => ?_⟩
  exact preservesColimitsOfShape_of_natIso
    ((sheafSections (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)).mapIso
      (smallEtalePostcomposeFinalIso B X U).op)

/-- **A finite shriek presentation makes a sheaf of modules finitely presentable.** If `F` is the
cokernel of a map between finite direct sums of extensions by zero of constant free rank-one module
sheaves, at étale objects all of whose coverings are refined by finite coverings with quasi-compact
fibre products, then `F` is a finitely presentable object of the category of sheaves of modules on
the small étale site.

This is the half of the module case of **Stacks 09Z4** that does not produce the presentation: a
cokernel is a coequalizer against the zero map, hence a colimit over a finite category of finitely
presentable objects. Stacks 095N is the statement that a constructible sheaf of modules over a
Noetherian ring on a quasi-compact quasi-separated scheme has such a presentation, and is not
proved here. -/
public theorem isFinitelyPresentable_of_hasFiniteShriekPresentation (B : BigEtaleSite.{u})
    (X : B.Scheme) (R : Type (u + 1)) [CommRing R]
    (P : SmallEtale B X.1 X.property → Prop)
    (hP : ∀ W, P W → (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings W)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (h : HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R P F) :
    IsFinitelyPresentable.{u + 1} F := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  obtain ⟨n, m, U, V, hU, hV, f, ⟨e⟩⟩ := h
  have hsig : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.1 X.property), (∀ i, P (W i)) →
      IsFinitelyPresentable.{u + 1}
        (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (W i)) := by
    intro k W hW
    have : ∀ j : Discrete (Fin k), IsFinitelyPresentable.{u + 1}
        ((Discrete.functor fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (W i)).obj j) := by
      rintro ⟨i⟩
      exact isFinitelyPresentable_moduleShriekConstant B X R (W i) (hP _ (hW i))
    exact isFinitelyPresentable_of_isColimit_of_finCategory _ (colimit.isColimit _)
  have h0 := hsig V hV
  have h1 := hsig U hU
  have hcoker : IsFinitelyPresentable.{u + 1} (cokernel f) := by
    have : ∀ j : WalkingParallelPair, IsFinitelyPresentable.{u + 1} ((parallelPair f 0).obj j) := by
      rintro (_ | _)
      · exact h0
      · exact h1
    exact isFinitelyPresentable_of_isColimit_of_finCategory _
      (colimit.isColimit (parallelPair f 0))
  let eF : cokernel f ≅ F :=
    (sheafToPresheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)).preimageIso
      (e ≪≫ Functor.isoWhiskerLeft F.obj (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} R) ≪≫
        F.obj.rightUnitor)
  exact isCardinalPresentable_of_iso eF _

/-- **Some sheaf of modules has a finite shriek presentation**, for every property `P` of étale
objects — the empty presentation, with no direct summands at all, presents the cokernel of the
identity of the empty direct sum. So the hypothesis of
`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation` is satisfiable, and in
particular `AlgebraicGeometry.HasFiniteShriekPresentation` is inhabited: nothing else in the
library constructs a value of it, since producing one from constructibility is Stacks 095N. -/
public theorem exists_hasFiniteShriekPresentation (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type (u + 1)) [CommRing R] (P : SmallEtale B X.1 X.property → Prop) :
    ∃ F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R P F := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  refine ⟨cokernel (𝟙 (∐ fun i : Fin 0 => moduleShriekConstant.{u, u + 1, u + 1} B X R
    (Fin.elim0 i))), 0, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0, 𝟙 _, ⟨?_⟩⟩
  exact (Functor.isoWhiskerLeft _ (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} R) ≪≫
    Functor.rightUnitor _).symm

/-- **The conclusion above is reached.** Taking the property of étale objects to be the
unsatisfiable one, the covering hypothesis is vacuous and the empty presentation applies, so a
finitely presentable sheaf of modules on the small étale site exists and no statement in this file
is conditional on an unexhibited hypothesis — beyond the ambient `AlgebraicGeometry.BigEtaleSite`,
which nothing in the library constructs. -/
public theorem exists_isFinitelyPresentable_moduleSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type (u + 1)) [CommRing R] :
    ∃ F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsFinitelyPresentable.{u + 1} F := by
  obtain ⟨F, hF⟩ := exists_hasFiniteShriekPresentation B X R (fun _ => False)
  exact ⟨F, isFinitelyPresentable_of_hasFiniteShriekPresentation B X R _
    (fun _ h => h.elim) F hF⟩

end AlgebraicGeometry

end
