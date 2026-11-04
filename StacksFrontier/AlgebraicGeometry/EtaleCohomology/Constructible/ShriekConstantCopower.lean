module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentableConstructibleUniverseLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantFree
public import StacksFrontier.CategoryTheory.Sites.Localization.CopowerModuleSheafCompatibility
public import StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseLift

/-!
# Stacks 03S8 for sheaves of modules over a ring in a universe of its own

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and `j : U ⟶ X` étale
with `U` quasi-compact and quasi-separated. Stacks 03S8 asserts that the sheaf
`j_{U!}\underline{\Lambda}_U` of `Λ`-modules is constructible. This file supplies what is
needed to prove it, and its flat refinement, for a ring `Λ : Type r` with modules in
`ModuleCat.{max (u + 1) r} Λ`, the universe extension by zero works in and the one Stacks 0960 is
stated at, rather than only for a ring in the module universe.

`AlgebraicGeometry.moduleShriekConstantIsoFree` identifies `j_{U!}\underline{\Lambda}_U` with
the free module sheaf on `h_U^#`, through `ModuleCat.free Λ : Type r ⥤ ModuleCat.{r} Λ`, which
carries the ring and the module in one universe. Here the free module functor is replaced by the
**copower** `ModuleCat.copower M : Type w ⥤ ModuleCat.{w} Λ` at
`M = ModuleCat.of Λ (ULift.{w} Λ)`, the same functor `E ↦ Λ^{(E)}` with the ring universe free,
together with its adjunction `ModuleCat.copowerAdj`.

The copower takes sheaves of sets in the *module* universe, so part (1) of the tag is used for a
sheaf of sets in `Type (max (u + 1) r)`, where `CategoryTheory.Sheaf.sheafifiedYoneda` does not
live. That is `AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`, for
the universe-polymorphic sheafified representable `CategoryTheory.Sheaf.sheafifiedUliftYoneda`.

## Main definitions

* `AlgebraicGeometry.moduleShriekConstantIsoCopower` — **the extension by zero of the constant
  free rank-one module sheaf is the copower module sheaf on `h_U^#`**, for a ring in any universe.
  This is `AlgebraicGeometry.moduleShriekConstantIsoFree` for a ring outside the module universe.

## Main results

* `CategoryTheory.Sheaf.copowerUliftSectionEquiv` and
  `CategoryTheory.Sheaf.coyonedaComposeAndSheafifyCopowerUliftIso` — the copower module sheaf on
  `h_U^#` corepresents the morphisms out of `M` into the sections over `U`.
* `CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyCopowerUlift` — the two
  spellings of `j_{U!}\underline{M}` agree, on any site with a terminal object, for a module in
  any universe containing that of the site.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_copower` and
  `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_copower` — the
  copower module sheaf by a finite, respectively finite free, module on a finite locally constant
  sheaf of sets is locally constant with finitely generated, respectively finite projective,
  values.

## Implementation notes

The corepresentation of `j_{U!}\underline{M}` is
`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso`, whose ring universe is already
free, that statement using only the constant-sheaf and sheaf-pullback adjunctions. The matching
corepresentation of the copower module sheaf is the copower adjunction transported to sheaves
followed by Yoneda's lemma
`CategoryTheory.Sheaf.uliftSectionEquiv` at the larger universe. The two corepresented functors
are literally the same — morphisms out of `M` into the sections — so no analogue of
`ModuleCat.coyonedaULiftSelfIso` is needed in between, and the comparison is the preimage under
the fully faithful `CategoryTheory.coyoneda` of their composite.

The three commutations the stratumwise argument needs — with inverse image to a stratum, with
restriction to a slice, and with the constant sheaf — are
`StacksFrontier.CategoryTheory.Sites.Localization.CopowerModuleSheafCompatibility`, the copower
analogues of the `ModuleCat.free` ones, and are already universe polymorphic.

The constructibility statements built on this file are the ones that carry the tag:
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible` and its
flat refinement in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek`.

Universes are supplied explicitly at several applications. They have to be: the module universe
`max u v s` of a statement determines `s` only through a `max`, and Lean has no solution for the
resulting constraint `max u v ?s =?= max u v s`, so a universe left to inference is reported as
stuck rather than solved.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe s v' u' v u w c r

attribute [local instance] ModuleCat.coyonedaObj_isRightAdjoint

namespace CategoryTheory.Sheaf

variable {C' : Type u'} [Category.{v'} C'] {C : Type u} [Category.{v} C]

/-- **Morphisms out of the copower module sheaf on a sheafified representable are morphisms out
of the module.** A morphism from the copower sheaf by `M` on `h_U^#` into `F` is a morphism from
`M` into the sections of `F` over `U`: the copower adjunction transported to sheaves, followed by
Yoneda's lemma for sheaves of sets at the larger universe.

The universe of the ring is free; only the module universe is tied to that of the site, the hom
sets of `Sheaf J A` living in `Type (max u v_A)` while those of `A` live in `Type v_A`. -/
public def copowerUliftSectionEquiv (J : GrothendieckTopology C) (R : Type r) [Ring R]
    (M : ModuleCat.{max u v s} R) [HasWeakSheafify J (ModuleCat.{max u v s} R)]
    [HasWeakSheafify J (Type max u v s)] (U : C) (F : Sheaf J (ModuleCat.{max u v s} R)) :
    ((composeAndSheafify J (ModuleCat.copower M)).obj
        ((sheafifiedUliftYoneda.{s} J).obj U) ⟶ F) ≃
      (coyoneda.obj (op M)).obj (F.obj.obj (op U)) :=
  ((adjunction J (ModuleCat.copowerAdj M)).homEquiv _ F).trans (uliftSectionEquiv J)

/-- **The copower module sheaf on `h_U^#` corepresents the morphisms out of `M` into the sections
over `U`.** The isomorphism of corepresented functors underlying
`CategoryTheory.Sheaf.copowerUliftSectionEquiv`. -/
public def coyonedaComposeAndSheafifyCopowerUliftIso (J : GrothendieckTopology C) (R : Type r)
    [Ring R] (M : ModuleCat.{max u v s} R) [HasWeakSheafify J (ModuleCat.{max u v s} R)]
    [HasWeakSheafify J (Type max u v s)] (U : C) :
    coyoneda.obj (op ((composeAndSheafify J (ModuleCat.copower M)).obj
        ((sheafifiedUliftYoneda.{s} J).obj U))) ≅
      (sheafSections J (ModuleCat.{max u v s} R)).obj (op U) ⋙ coyoneda.obj (op M) :=
  NatIso.ofComponents (fun F => Equiv.toIso (copowerUliftSectionEquiv J R M U F)) (by
    intro F G φ
    ext α
    change uliftSectionEquiv J ((adjunction J (ModuleCat.copowerAdj M)).homEquiv _ _ (α ≫ φ)) = _
    rw [(adjunction J (ModuleCat.copowerAdj M)).homEquiv_naturality_right,
      uliftSectionEquiv_comp]
    rfl)

/-- **The two spellings of `j_{U!}\underline{M}` agree, for a module in any universe containing
that of the site.** For a continuous functor `π` out of a site with terminal object `T`, the sheaf
pullback along `π` of the constant sheaf at `M` is the copower module sheaf by `M` on the
sheafified representable at `π.obj T`.

Both corepresent the morphisms from `M` into the sections over `π.obj T` — the second by
`CategoryTheory.Sheaf.coyonedaComposeAndSheafifyCopowerUliftIso`, the first by
`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso` — and `CategoryTheory.coyoneda` is
fully faithful. Neither mentions `ModuleCat.free`, which is what ties the ring universe to the
module universe in `CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree`. -/
public def sheafPullbackConstantSheafIsoComposeAndSheafifyCopowerUlift (π : C' ⥤ C)
    (JC' : GrothendieckTopology C') (JC : GrothendieckTopology C) [π.IsContinuous JC' JC]
    (R : Type r) [Ring R] (M : ModuleCat.{max u v s} R)
    [HasWeakSheafify JC' (ModuleCat.{max u v s} R)]
    [HasWeakSheafify JC (ModuleCat.{max u v s} R)] [HasWeakSheafify JC (Type max u v s)]
    [∀ F : C'ᵒᵖ ⥤ ModuleCat.{max u v s} R, π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) :
    (Functor.sheafPullbackConstruction.sheafPullback π (ModuleCat.{max u v s} R) JC' JC).obj
        ((constantSheaf JC' (ModuleCat.{max u v s} R)).obj M) ≅
      (composeAndSheafify JC (ModuleCat.copower M)).obj
        ((sheafifiedUliftYoneda.{s} JC).obj (π.obj T)) :=
  by
  have e₁ : coyoneda.obj (op ((composeAndSheafify JC (ModuleCat.copower M)).obj
        ((sheafifiedUliftYoneda.{s} JC).obj (π.obj T)))) ≅
      (sheafSections JC (ModuleCat.{max u v s} R)).obj (op (π.obj T)) ⋙ coyoneda.obj (op M) :=
    coyonedaComposeAndSheafifyCopowerUliftIso JC R M (π.obj T)
  have e₂ : coyoneda.obj (op ((Functor.sheafPullbackConstruction.sheafPullback π
          (ModuleCat.{max u v s} R) JC' JC).obj
        ((constantSheaf JC' (ModuleCat.{max u v s} R)).obj M))) ≅
      (sheafSections JC (ModuleCat.{max u v s} R)).obj (op (π.obj T)) ⋙ coyoneda.obj (op M) :=
    coyonedaSheafPullbackConstantSheafIso.{v', u', v, u, r, s} π JC' JC R hT M
  exact (Coyoneda.fullyFaithful.preimageIso (e₁.trans e₂.symm)).unop

end CategoryTheory.Sheaf

namespace Stacks.ConstantSheaf

/-- **The copower module sheaf by a finite free module on a finite locally constant sheaf of sets
is locally constant with finite projective values.** A trivializing covering of the sheaf of sets
serves for the copower sheaf, with constant value the copower of `M` by the finite constant
value, which is finite and free, hence finite projective.

This is `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_free` with the
copower in place of the free module functor, and so without the pin tying the universe of the
ring to that of the modules. -/
public theorem isFiniteProjectiveLocallyConstant_composeAndSheafify_copower
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
    (M : ModuleCat.{w} R) [Module.Finite R M] [Module.Free R M]
    [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type w)]
    [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
      (Over.forget V).op.HasPointwiseRightKanExtension G]
    (F : Sheaf J (Type w)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteProjectiveLocallyConstant R J
      ((CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.copower M)).obj F) := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Finite E := hE
  refine ⟨(ModuleCat.copower M).obj E, ModuleCat.moduleFinite_copower_obj M E,
    inferInstance, ⟨?_⟩⟩
  exact ((CategoryTheory.Sheaf.constantSheafComposeAndSheafifyModuleCopowerIso (J.over (V i)) M
        Over.mkIdTerminal).app E).symm ≪≫
    (CategoryTheory.Sheaf.composeAndSheafify (J.over (V i)) (ModuleCat.copower M)).mapIso e ≪≫
    ((CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerOverPullbackIso J M (V i)).app F).symm

/-- **The copower module sheaf by a finite module on a finite locally constant sheaf of sets is
locally constant with finitely generated values.** A trivializing covering of the sheaf of sets
serves for the copower sheaf, with constant value the copower of `M` by the finite constant
value.

This is `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_free` with the
copower in place of the free module functor, and so without the pin tying the universe of the
ring to that of the modules. -/
public theorem isFiniteTypeLocallyConstant_composeAndSheafify_copower
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
    (M : ModuleCat.{w} R) [Module.Finite R M]
    [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type w)]
    [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
      (Over.forget V).op.HasPointwiseRightKanExtension G]
    (F : Sheaf J (Type w)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteTypeLocallyConstant R J
      ((CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.copower M)).obj F) := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Finite E := hE
  refine ⟨(ModuleCat.copower M).obj E,
    (ModuleCat.isFG_iff _).2 (ModuleCat.moduleFinite_copower_obj M E), ⟨?_⟩⟩
  exact ((CategoryTheory.Sheaf.constantSheafComposeAndSheafifyModuleCopowerIso (J.over (V i)) M
        Over.mkIdTerminal).app E).symm ≪≫
    (CategoryTheory.Sheaf.composeAndSheafify (J.over (V i)) (ModuleCat.copower M)).mapIso e ≪≫
    ((CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerOverPullbackIso J M (V i)).app F).symm

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- **The extension by zero of the constant free rank-one module sheaf is the copower module
sheaf on `h_U^#`**, for a ring in any universe.

This is `AlgebraicGeometry.moduleShriekConstantIsoFree` with the restriction to a ring in the
module universe removed: the copower by the free rank-one module replaces `ModuleCat.free Λ`, and
the sheaf of sets it is applied to is the sheafified representable of the module universe. The
image of the terminal object of the small étale site of `U` under composition with `U ⟶ X` is
`AlgebraicGeometry.smallEtalePostcomposeFinalIso`-isomorphic to `U`, not equal to it. -/
public def moduleShriekConstantIsoCopower (U : SmallEtale B X.1 X.property) :
    moduleShriekConstant.{u, r, r} B X Λ U ≅
      (Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
          (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))).obj
        ((Sheaf.sheafifiedUliftYoneda.{r} (SmallEtale.topology B X.1 X.property)).obj U) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B U.obj.left Λ
  exact (Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyCopowerUlift.{r, u, u + 1, u, u + 1}
      (smallEtalePostcompose B X.1 X.property U) _ _ Λ
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))
      (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)).trans
    ((Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))).mapIso
        ((Sheaf.sheafifiedUliftYoneda.{r} (SmallEtale.topology B X.1 X.property)).mapIso
          (smallEtalePostcomposeFinalIso B X U)))

end AlgebraicGeometry

end
