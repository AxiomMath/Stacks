module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleObjectStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekCharacterization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekConstantCopower
public import StacksFrontier.CategoryTheory.Sites.Localization.FreeModuleSheafCompatibility
public import StacksCore.Tactic.StacksAttribute

/-!
# The generators of a shriek presentation are constructible

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and `Λ` a Noetherian
ring. Stacks 03S8 asserts that for `j : U ⟶ X` an étale morphism with `U` quasi-compact and
quasi-separated the sheaf `h_U` of sets, and the sheaf `j_{U!}\underline{\Lambda}_U` of
`Λ`-modules, are constructible. Both are proved here, the second from the first: by
`AlgebraicGeometry.moduleShriekConstantIsoCopower` the module sheaf is the copower module sheaf
by the free rank-one module on `h_U^#`, and constructibility transfers across the copower module
sheaf functor.

The coefficient ring lives in a universe `r` of its own, the sheaves of modules in
`ModuleCat.{max (u + 1) r} Λ`. That is why the copower appears instead of `ModuleCat.free Λ`,
whose source `Type r ⥤ ModuleCat.{r} Λ` would force the ring into the module universe; see the
implementation notes.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_free` — the free module
  sheaf on a finite locally constant sheaf of sets is locally constant with finitely generated
  values, on any site.
* `AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_free` — **constructibility
  transfers across the free module sheaf functor**: the free module sheaf on a constructible sheaf
  of sets is a constructible sheaf of modules.
* `AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_copower` — the same for the
  copower module sheaf functor, with the universe of the ring free.
* `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` — **Stacks 03S8 part (1)**,
  unconditionally: `h_U` is a constructible sheaf of sets.
* `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` — **Stacks 03S8 for sheaves
  of modules**: `j_{U!}\underline{\Lambda}_U` is a constructible sheaf of `Λ`-modules, for a
  Noetherian commutative ring `Λ : Type r` in an arbitrary universe. This is the
  hypothesis `hshriek` of
  `AlgebraicGeometry.isConstructibleModuleSheaf_iff_affineShriekPresentation` and of its
  quasi-compact quasi-separated companion.
* `AlgebraicGeometry.isConstructibleModuleSheaf_iff_affineShriekPresentation_of_gen` — Stacks 095N
  at the affine presentation with `hshriek` discharged, so that only the finite generation step
  remains as a hypothesis.

## Implementation notes

Constructibility of a sheaf of sets and of a sheaf of modules are the same condition — on every
affine open there is a finite constructible stratification on whose strata the inverse image of
the sheaf is locally constant with finite, respectively finitely generated, values — so the
transfer needs exactly that the free module sheaf functor commute with the three operations
occurring in that condition. The three isomorphisms are
`CategoryTheory.Sheaf.composeAndSheafifyFreeSheafPullbackIso`,
`CategoryTheory.Sheaf.composeAndSheafifyFreeOverPullbackIso` and
`CategoryTheory.Sheaf.constantSheafComposeAndSheafifyFreeIso`; with them the *same* stratification
and the *same* trivializing coverings serve for the module sheaf, the constant value `E` being
replaced by the free module `Λ^{(E)}`, which is finitely generated because `E` is finite.

The terminal object of the localized site `(J/V)` used by the constant-sheaf comparison is
`CategoryTheory.Over.mkIdTerminal`, so no terminal object of the small étale site itself is
needed.

For the module statement at a ring in a universe of its own the same three isomorphisms are used
for the copower module sheaf instead —
`CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso`,
`CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerOverPullbackIso` and
`CategoryTheory.Sheaf.constantSheafComposeAndSheafifyModuleCopowerIso` — and the sheaf of sets is
taken in the module universe, where the copower functor accepts it: part (1) of the tag enters as
`AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`. The free-module form
`AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_free` is kept as the statement
about `ModuleCat.free`; it is the case `r = u + 1`.

Part (1) of Stacks 03S8 is `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, which
carries the conclusion of Stacks 03S0 as an explicit hypothesis; that hypothesis is now proved,
`AlgebraicGeometry.hasFiniteEtaleStratification`, so the tag is restated here with nothing
granted.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u r

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type w) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, HasWeakSheafify (J.over V) (Type w)]
  [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G]

omit [HasWeakSheafify J (Type w)] in
/-- **The free module sheaf on a finite locally constant sheaf of sets is locally constant with
finitely generated values.** A trivializing covering of the sheaf of sets serves for the free
module sheaf, with constant value the free module on the finite constant value. -/
public theorem isFiniteTypeLocallyConstant_composeAndSheafify_free
    (F : Sheaf J (Type w)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteTypeLocallyConstant R J
      ((Sheaf.composeAndSheafify J (ModuleCat.free R)).obj F) := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  refine ⟨(ModuleCat.free R).obj E, ?_, ⟨?_⟩⟩
  · change Module.Finite R (E →₀ R)
    infer_instance
  · exact ((Sheaf.constantSheafComposeAndSheafifyFreeIso (J.over (V i)) R
        Over.mkIdTerminal).app E).symm ≪≫
      (Sheaf.composeAndSheafify (J.over (V i)) (ModuleCat.free R)).mapIso e ≪≫
      ((Sheaf.composeAndSheafifyFreeOverPullbackIso J R (V i)).app F).symm

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R]

/-- **Stacks 03S8, part (1).** For an étale morphism `j : U ⟶ X` of quasi-compact and
quasi-separated schemes, presented as an object `U` of the small étale site of `X`, the sheaf
`h_U` represented by `U` is a constructible sheaf of sets on `X_étale`.

This is `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda` with its hypothesis, the
conclusion of Stacks 03S0, discharged by `AlgebraicGeometry.hasFiniteEtaleStratification`. -/
@[stacks 03S8 "part (1), sheaves of sets"]
public theorem isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) :=
  isConstructibleSetSheaf_sheafifiedYoneda B X U
    (hasFiniteEtaleStratification B X U ‹_› ‹_› ⟨‹_›, ‹_›⟩)

section GeneralRingUniverse

attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

omit [IsNoetherianRing Λ] in
/-- **Constructibility transfers across the copower module sheaf functor.** The copower module
sheaf by a finite `Λ`-module on a constructible sheaf of sets on `X_étale` is a constructible
sheaf of `Λ`-modules.

This is `AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_free` with the universe
of the ring free: the stratification furnished by the sheaf of sets serves, the copower module
sheaf commutes with inverse image to a stratum, and on a stratum it carries a finite locally
constant sheaf to a locally constant sheaf with finitely generated values. The sheaf of sets is
taken in the module universe, which is where the copower functor accepts it. -/
public theorem isConstructibleModuleSheaf_composeAndSheafify_copower
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type max (u + 1) r))
    (hF : IsConstructibleFiniteSheaf B X F) :
    IsConstructibleModuleSheaf B X Λ
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
        (ModuleCat.copower M)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    ((Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso
      (SmallEtale.topology B X.obj X.property) M
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (smallEtaleBaseChange B (s.inclusion i))).app F).symm ?_
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_copower _ Λ M _ (hs i)

omit [IsNoetherianRing Λ] in
/-- **Stacks 03S8 for sheaves of modules.** For `U` a quasi-compact quasi-separated object of the
small étale site of a quasi-compact quasi-separated scheme `X` and `Λ` a Noetherian commutative
ring in an arbitrary universe `r`, the extension by zero `j_{U!}\underline{\Lambda}_U` of the
constant free rank-one module sheaf is a constructible sheaf of `Λ`-modules in
`ModuleCat.{max (u + 1) r} Λ`.

By `AlgebraicGeometry.moduleShriekConstantIsoCopower` this sheaf is the copower module sheaf by
the free rank-one module on the sheaf `h_U^#` of sets, which is constructible as a sheaf of sets
in the module universe by
`AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`, part (1) of the same
tag. The copower stands in for `ModuleCat.free Λ`, whose source `Type r ⥤ ModuleCat.{r} Λ` would
force the ring into the module universe. -/
@[stacks 03S8 "sheaves of modules over a Noetherian commutative ring in an arbitrary universe: \
an extension by zero of a constant free rank-one module sheaf at a quasi-compact \
quasi-separated etale object is constructible"]
public theorem isConstructibleModuleSheaf_moduleShriekConstant
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) := by
  exact isStratifiedSheaf_congr B X _
    (fun T _ _ e' h ↦ Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ e' h)
    (moduleShriekConstantIsoCopower B X Λ U).symm
    (isConstructibleModuleSheaf_composeAndSheafify_copower B X Λ
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) _
      (isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs.{r} B X U))

end GeneralRingUniverse

variable [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} R)]

omit [IsNoetherianRing R] in
/-- **Constructibility transfers across the free module sheaf functor.** The free sheaf of
`R`-modules on a constructible sheaf of sets on `X_étale` is a constructible sheaf of
`R`-modules.

The stratification furnished by the sheaf of sets serves: the free module sheaf commutes with
inverse image to a stratum, and on a stratum it carries a finite locally constant sheaf to a
locally constant sheaf with finitely generated values. -/
public theorem isConstructibleModuleSheaf_composeAndSheafify_free
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleModuleSheaf B X R
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
        (ModuleCat.free R)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ R
    ((Sheaf.composeAndSheafifyFreeSheafPullbackIso
      (SmallEtale.topology B X.obj X.property) R
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (smallEtaleBaseChange B (s.inclusion i))).app F).symm ?_
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_free _ R _ (hs i)

/-- **Stacks 095N, the affine presentation, with `hshriek` discharged.** Let `X` be a
quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring. A sheaf of `Λ`-modules on
`X_étale` is constructible exactly when it is the cokernel of a map between finite direct sums of
extensions by zero of constant free rank-one module sheaves at affine objects of `X_étale`.

Only the finite generation step `hgen` of the proof remains as a hypothesis; constructibility of
the generators is `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`. -/
@[stacks 095N "affine presentation, carrying as the only explicit hypothesis the finite \
generation step of the proof (hgen), that a constructible sheaf of modules is a quotient of a \
finite direct sum of extensions by zero of constant free rank-one module sheaves"]
public theorem isConstructibleModuleSheaf_iff_affineShriekPresentation_of_gen
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hgen : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
          (∀ i, SmallEtale.IsAffine B X.obj X.property (U i)) ∧
          ∃ p : (∐ fun i ↦ moduleShriekConstant.{u, u + 1, u + 1} B X R (U i)) ⟶ G, Epi p)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R)) :
    IsConstructibleModuleSheaf B X R F ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
        (SmallEtale.IsAffine B X.obj X.property) F :=
  isConstructibleModuleSheaf_iff_affineShriekPresentation B X R
    (fun U hU ↦ by
      have hA : IsAffine ((SmallEtale.toScheme B X.obj X.property).obj U) := hU
      have hc : CompactSpace U.obj.left.obj :=
        inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U))
      have hq : QuasiSeparatedSpace U.obj.left.obj :=
        inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj U))
      exact isConstructibleModuleSheaf_moduleShriekConstant B X R U)
    hgen F

end AlgebraicGeometry

end
