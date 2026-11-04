module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekCharacterization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentablePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale sheaves as filtered colimits of constructible ones

Let `X` be a quasi-compact and quasi-separated scheme. Every sheaf of sets on the small étale
site of `X` is a filtered colimit of constructible sheaves of sets, and for a Noetherian ring
`Λ` every sheaf of `Λ`-modules is a filtered colimit of constructible sheaves of `Λ`-modules
(Stacks 03SA, parts (1) and (3)). Each is the composite of two inputs: a presentation of an
arbitrary sheaf as a filtered colimit of sheaves built from finitely many quasi-compact
quasi-separated étale objects (Stacks 093C), and the constructibility of the sheaves so built
(Stacks 03S8 together with Stacks 03RZ).

The second input is what this file assembles. Constructibility is a weak Serre condition — Stacks
03RZ, available here as
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` for module
coefficients and as `AlgebraicGeometry.Constructible.constructibleAbelianSheaf_isWeakSerreClass`
for abelian ones — and closure under finite limits and colimits for sheaves of sets is
`AlgebraicGeometry.isConstructibleSetSheaf_colimit`. So a finite coproduct of constructible
sheaves is constructible, and so is the cokernel or coequalizer of a map between two of them.
Feeding in the constructibility of the generators turns each presentation into a
constructibility statement, and composing with Stacks 093C gives Stacks 03SA. For module
coefficients that step is already in the library, as
`AlgebraicGeometry.isConstructibleModuleSheaf_of_hasFiniteShriekPresentation` (one direction of
Stacks 095N); only the sheaves-of-sets and the abelian forms are carried out here.

The same argument gives one of the two inclusions of Stacks 09YT: a cokernel of a map between
finite direct sums of the sheaves `j_{U!}(Z/nZ)_U`, at quasi-compact quasi-separated étale
objects `U` and positive integers `n`, is a constructible abelian sheaf.

## Hypotheses that are granted rather than proved

Two statements of the source are quantified over as explicit hypotheses, because this library
does not have them. They are named so that what each theorem below assumes is visible as a
single binder, in the style of
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`.

* **Stacks 03S0**, that an étale morphism of quasi-compact quasi-separated schemes becomes
  finite étale on the strata of a partition of its target into constructible locally closed
  subschemes, as `AlgebraicGeometry.EtaleFiniteStratificationExists`. Part (1) of Stacks 03S8 is
  in the library, as `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, and carries
  exactly this hypothesis; so the sheaves-of-sets statement below carries Stacks 03S0 and not
  Stacks 03S8.
* **Stacks 03S8 for coefficients**, which the library does not have. For module coefficients it
  is the hypothesis `hshriek` of
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_hasFiniteShriekPresentation`, reused verbatim
  below rather than renamed. For abelian coefficients it is part (2) of the tag, at the finite
  abelian groups `Z/nZ`, as `AlgebraicGeometry.AbelianShriekZModIsConstructible`.
* **Stacks 093C** in the two spellings the étale presentations use. The module case of 093C is
  proved in this library, as
  `Stacks.Sites.isFilteredColimit_of_hasEnoughQuasiCompactObjects`, but for sheaves of modules
  over a *sheaf of rings* on a site equipped with a
  `Stacks.Sites.QuasiCompactObjectsSituation`, and neither that situation for the small étale
  site nor the comparison of `Stacks.Sites.extensionByZeroUnit` with
  `AlgebraicGeometry.moduleShriekConstant` exists here. The two spellings needed are
  `AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations` and
  `AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations`.

## Main definitions

* `AlgebraicGeometry.IsQCQSEtaleObject` — the étale objects the presentations are built from.
* `AlgebraicGeometry.EtaleFiniteStratificationExists` — Stacks 03S0, carried as a hypothesis.
* `AlgebraicGeometry.abelianShriekZMod` — the abelian sheaf `j_{U!}(Z/nZ)_U`.
* `AlgebraicGeometry.HasFiniteZModShriekPresentation` — the displayed form of Stacks 09YT, at a
  prescribed property of the étale objects.

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf` — Stacks 03SA (1).
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf` — Stacks 03SA (3).
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_affineZModShriekPresentation` — the inclusion
  of the displayed cokernels of Stacks 09YT into the constructible abelian sheaves, in the
  quasi-compact quasi-separated and in the affine form.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_presentation` — the step of the proof of
  Stacks 03SA (1) that turns a presentation into constructibility; the module analogue is the
  library's `AlgebraicGeometry.isConstructibleModuleSheaf_of_hasFiniteShriekPresentation`.

## Implementation notes

The coefficient universe of the module statements is `ModuleCat.{u + 1} Λ` for `Λ : Type (u + 1)`
and is not free: `AlgebraicGeometry.HasFiniteShriekPresentation` is built from
`AlgebraicGeometry.moduleShriekConstant`, whose finite presentability — and hence everything in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable` — is stated
only at the ring and module universe `u + 1`, while
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` is stated at
`ModuleCat.{max (u + 1) w}`. Taking `w` to be `u + 1` makes the two agree. The two sheafification
side conditions of `AlgebraicGeometry.IsConstructibleModuleSheaf` are therefore restated at that
universe as `AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCatSelf` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCatSelf`, which is also what discharges
the two instance arguments of the library's Stacks 095N at this universe; the generic site-level
instance for a localization of the site has coefficient universe `max (u + 1) u w`, so instance
search on the goal `ModuleCat.{u + 1}` stalls on a `max` constraint unless the specialisation is
in the local context; naming it with `letI` before stating a `Prop` whose coefficient universe is
only determined by an argument is the remedy.

The conclusions quantify over a diagram, a cocone whose point is literally the given sheaf, and
`Nonempty (IsColimit _)` — the spelling of
`Stacks.Sites.isFilteredColimit_of_hasEnoughQuasiCompactObjects`, this library's form of
Stacks 093C. `IsColimit` is data, so `Nonempty` is what makes the statement a proposition; no
other part of either conclusion is behind a `Nonempty`.

Stacks 03SA (3) does not use the quasi-compactness and quasi-separatedness of `X`: both granted
inputs hold only for such an `X`, and given them the conclusion follows with no further
geometric input, so the binders would be unused. The statement is therefore formally stronger
than the tag, not weaker.

## References

* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- Quasi-compactness and quasi-separatedness of the scheme underlying an étale object of the
small étale site of `X`. This is the collection `B` of the proof of Stacks 03SA, the
quasi-compact quasi-separated objects of `X_étale`. -/
public abbrev IsQCQSEtaleObject (U : SmallEtale B X.obj X.property) : Prop :=
  CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U) ∧
    QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj U)

/-! ### Sheaves of sets -/

/-- **Stacks 03S0 as a hypothesis.** An étale morphism of quasi-compact quasi-separated schemes
becomes finite étale on the strata of a partition of its target into constructible locally closed
subschemes. The conclusion is `AlgebraicGeometry.HasFiniteEtaleStratification`, the predicate that
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda` — this library's Stacks 03S8 (1) —
also carries; it is a statement about the morphism alone and mentions no sheaf. -/
public def EtaleFiniteStratificationExists : Prop :=
  ∀ (Y : B.Scheme) (U : SmallEtale B Y.obj Y.property), CompactSpace Y.obj →
    QuasiSeparatedSpace Y.obj → IsQCQSEtaleObject B Y U → HasFiniteEtaleStratification B Y U

/-- Constructibility of a sheaf of sets transports along an isomorphism: the stratification of
an affine open furnished by one of the two sheaves works for the other, since inverse image to a
stratum carries the isomorphism along. -/
public theorem isConstructibleSetSheaf_congr
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (e : F ≅ G)
    (hF : IsConstructibleSetSheaf B X F) : IsConstructibleSetSheaf B X G := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  have := hs i
  exact isFiniteLocallyConstant_congr _ ((smallEtaleSetPullback B (s.inclusion i)).mapIso e)

/-- A finite coproduct of constructible sheaves of sets is constructible, a finite coproduct
being a colimit over a finite discrete category and Stacks 03RZ (1) giving closure under finite
colimits. -/
public theorem isConstructibleSetSheaf_sigma {n : ℕ}
    (Z : Fin n → Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hZ : ∀ i, IsConstructibleSetSheaf B X (Z i)) :
    IsConstructibleSetSheaf B X (∐ Z) :=
  isConstructibleSetSheaf_colimit B X (Discrete.functor Z) (by rintro ⟨i⟩; exact hZ i)

/-- Each representable `h_U` at a quasi-compact quasi-separated étale object of a quasi-compact
quasi-separated scheme is constructible, granted Stacks 03S0. This is the library's Stacks
03S8 (1), `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, with the quasi-compactness
and quasi-separatedness moved out of the instance binders. -/
public theorem isConstructibleSetSheaf_sheafifiedYoneda_of_stratification
    (h03S0 : EtaleFiniteStratificationExists B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj) (U : SmallEtale B X.obj X.property)
    (hU : IsQCQSEtaleObject B X U) :
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) := by
  have hc : CompactSpace U.obj.left.obj := hU.1
  have hq : QuasiSeparatedSpace U.obj.left.obj := hU.2
  have hxc : CompactSpace X.obj := hXc
  have hxq : QuasiSeparatedSpace X.obj := hXq
  exact isConstructibleSetSheaf_sheafifiedYoneda B X U (h03S0 X U hXc hXq hU)

/-- **The coequalizers of the proof of Stacks 03SA (1) are constructible.** A sheaf of sets
presented as a coequalizer of two maps between finite coproducts of sheaves represented by
quasi-compact quasi-separated étale objects is constructible, granted Stacks 03S0.

The representables are constructible by Stacks 03S8 (1), the two coproducts by
`AlgebraicGeometry.isConstructibleSetSheaf_sigma`, and the coequalizer is a colimit over
`CategoryTheory.Limits.WalkingParallelPair`, which is a finite category, so Stacks 03RZ (1)
applies again. -/
public theorem isConstructibleSetSheaf_of_presentation
    (h03S0 : EtaleFiniteStratificationExists B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : HasFiniteQCSRepresentableCoequalizerPresentation B X F) :
    IsConstructibleSetSheaf B X F := by
  obtain ⟨n, m, U, V, hU, hV, f, g, ⟨e⟩⟩ := hF
  have hsum : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.obj X.property),
      (∀ i, IsQCQSEtaleObject B X (W i)) → IsConstructibleSetSheaf B X
        (∐ fun i =>
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (W i)) :=
    fun W hW => isConstructibleSetSheaf_sigma B X _ fun i =>
      isConstructibleSetSheaf_sheafifiedYoneda_of_stratification B X h03S0 hXc hXq (W i) (hW i)
  refine isConstructibleSetSheaf_congr B X e ?_
  exact isConstructibleSetSheaf_colimit B X (parallelPair f g)
    (by rintro (_ | _); exacts [hsum V hV, hsum U hU])

/-- **Stacks 093C (1) as a hypothesis**, in the spelling of
`AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation`: every sheaf of sets on the
small étale site of `X` is a filtered colimit of coequalizers of maps between finite coproducts
of sheaves represented by quasi-compact quasi-separated étale objects.

This library has no form of Stacks 093C for sheaves of sets on a site. -/
public def SetSheavesAreFilteredColimitsOfPresentations : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, HasFiniteQCSRepresentableCoequalizerPresentation B X (D.obj i)

/-- **Stacks 03SA (1).** Let `X` be a quasi-compact and quasi-separated scheme and `F` a sheaf of
sets on `X_étale`. Then `F` is a filtered colimit of constructible sheaves of sets.

This is the source's own proof: Stacks 093C writes `F` as a filtered colimit of coequalizers of
maps between finite coproducts of representables at quasi-compact quasi-separated objects, and
`AlgebraicGeometry.isConstructibleSetSheaf_of_presentation` says those coequalizers are
constructible. Of the three cited inputs, Stacks 03S8 (1) and Stacks 03RZ (1) are discharged from
the library; what remains as hypotheses is Stacks 093C, and Stacks 03S0, which Stacks 03S8 (1)
itself carries. -/
@[stacks 03SA "part (1), granted Stacks 093C (1) in the coequalizer spelling as the hypothesis \
  h093C and Stacks 03S0 as the hypothesis h03S0; Stacks 03S8 (1) and Stacks 03RZ (1) are \
  discharged from the library"]
public theorem exists_isFilteredColimit_isConstructibleSetSheaf
    (h093C : SetSheavesAreFilteredColimitsOfPresentations B X)
    (h03S0 : EtaleFiniteStratificationExists B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleSetSheaf B X (D.obj i) := by
  obtain ⟨I, hI, hfilt, D, ι, hcolim, hD⟩ := h093C F
  exact ⟨I, hI, hfilt, D, ι, hcolim,
    fun i => isConstructibleSetSheaf_of_presentation B X h03S0 hXc hXq (hD i)⟩

/-! ### Sheaves of modules over a Noetherian ring -/

section Modules

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- Pushforward of sheaves of `Λ`-modules along small étale base change is a right adjoint, at
the coefficient universe `u + 1` at which the shriek presentations are stated.

`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat` is the same statement at
`ModuleCat.{max (u + 1) w} Λ` for `Λ : Type r`; this is the instance at `w = r = u + 1`. -/
public instance SmallEtale.isRightAdjointPushforward_moduleCatSelf
    {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

/-- Presheaves of `Λ`-modules on a localization of the small étale site admit weak
sheafification, at the coefficient universe `u + 1` at which the shriek presentations are
stated. This is what local constancy of finite type asks for, the local value of such a sheaf
being a constant sheaf on a slice. -/
public instance SmallEtale.hasWeakSheafifyOver_moduleCatSelf (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, u + 1} B Λ T V

/-- **Stacks 093C (2) as a hypothesis**, in the spelling of
`AlgebraicGeometry.HasFiniteShriekPresentation`: every sheaf of `Λ`-modules on the small étale
site of `X` is a filtered colimit of cokernels of maps between finite direct sums of the sheaves
`j_{U!}Λ` at quasi-compact quasi-separated étale objects `U`.

`Stacks.Sites.isFilteredColimit_of_hasEnoughQuasiCompactObjects` is this library's Stacks 093C
(2), for sheaves of modules over a sheaf of rings on a site with a
`Stacks.Sites.QuasiCompactObjectsSituation`; transporting it here would need that situation for
the small étale site and a comparison of the two extensions by zero, neither of which exists. -/
public def ModuleSheavesAreFilteredColimitsOfPresentations : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ),
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, HasFiniteShriekPresentation.{u, u + 1, u + 1} B X Λ
          (IsQCQSEtaleObject B X) (D.obj i)

/-- **Stacks 03SA (3).** Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a Noetherian
ring and `F` a sheaf of `Λ`-modules on `X_étale`. Then `F` is a filtered colimit of constructible
sheaves of `Λ`-modules.

This is the source's own proof: Stacks 093C writes `F` as a filtered colimit of cokernels of maps
between finite direct sums of the sheaves `j_{U!}Λ` at quasi-compact quasi-separated objects, and
the library's Stacks 095N says those cokernels are constructible once the generators are — that is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_hasFiniteShriekPresentation`. Stacks 03RZ (3) is
discharged from the library; what remains as hypotheses is Stacks 093C and the
sheaves-of-modules case of Stacks 03S8. -/
@[stacks 03SA "part (3), granted Stacks 093C (2) in the shriek spelling as the hypothesis h093C \
  and the sheaves-of-modules case of Stacks 03S8 as the hypothesis hshriek, which is the same \
  hypothesis the library's Stacks 095N carries; Stacks 03RZ (3) is discharged from the library"]
public theorem exists_isFilteredColimit_isConstructibleModuleSheaf
    (h093C : ModuleSheavesAreFilteredColimitsOfPresentations B X Λ)
    (hshriek : ∀ U : SmallEtale B X.obj X.property, IsQCQSEtaleObject B X U →
      IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, u + 1, u + 1} B X Λ U))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleModuleSheaf B X Λ (D.obj i) := by
  obtain ⟨I, hI, hfilt, D, ι, hcolim, hD⟩ := h093C F
  exact ⟨I, hI, hfilt, D, ι, hcolim,
    fun i => isConstructibleModuleSheaf_of_hasFiniteShriekPresentation B X Λ _ hshriek _ (hD i)⟩

end Modules

/-! ### Abelian sheaves -/

/-- The abelian sheaf `j_{U!}(Z/nZ)_U` on the small étale site of `X`: extension by zero along
the étale object `U` of the constant sheaf with value `Z/nZ`. -/
public def abelianShriekZMod (n : ℕ) (U : SmallEtale B X.obj X.property) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  (abelianExtensionByZero B X.obj X.property U).obj
    ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))

/-- **Stacks 03S8 (2) as a hypothesis**, at the finite abelian groups `Z/nZ`. For `j : U → Y` an
étale morphism of quasi-compact quasi-separated schemes and `n` a positive integer, `j_!(Z/nZ)`
is a constructible abelian sheaf. This is not proved in this library, for the same reason as
part (1); `ZMod n` is finite precisely because `n` is positive. -/
public def AbelianShriekZModIsConstructible : Prop :=
  ∀ (Y : B.Scheme) (U : SmallEtale B Y.obj Y.property) (n : ℕ), 0 < n → CompactSpace Y.obj →
    QuasiSeparatedSpace Y.obj → IsQCQSEtaleObject B Y U →
    IsConstructibleAbelianSheaf B Y (abelianShriekZMod B Y n U)

/-- The displayed form of Stacks 09YT, at a prescribed property `P` of the étale objects: `F` is
the cokernel of a map `⨁_{j = 1, …, m} j_{V_j!}(Z/m_jZ) ⟶ ⨁_{i = 1, …, n} j_{U_i!}(Z/n_iZ)` with
the `V_j` and `U_i` objects of `X_étale` satisfying `P` and the `m_j`, `n_i` positive integers.
The tag states it both for `P` the quasi-compact quasi-separated objects and for `P` the affine
ones. -/
public def HasFiniteZModShriekPresentation (P : SmallEtale B X.obj X.property → Prop)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → SmallEtale B X.obj X.property)
      (V : Fin m → SmallEtale B X.obj X.property) (a : Fin n → ℕ) (b : Fin m → ℕ),
    (∀ i, P (U i)) ∧ (∀ j, P (V j)) ∧ (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      ∃ f : (∐ fun j => abelianShriekZMod B X (b j) (V j)) ⟶
        (∐ fun i => abelianShriekZMod B X (a i) (U i)), Nonempty (cokernel f ≅ F)

/-- A presentation by affine étale objects is one by quasi-compact quasi-separated étale objects:
an affine scheme is a quasi-compact and quasi-separated space. -/
public theorem hasFiniteZModShriekPresentation_qcqs_of_affine
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (h : HasFiniteZModShriekPresentation B X (SmallEtale.IsAffine B X.obj X.property) F) :
    HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) F := by
  obtain ⟨n, m, U, V, a, b, hU, hV, ha, hb, f, e⟩ := h
  refine ⟨n, m, U, V, a, b, fun i => ?_, fun j => ?_, ha, hb, f, e⟩
  · have := hU i
    exact ⟨inferInstance, inferInstance⟩
  · have := hV j
    exact ⟨inferInstance, inferInstance⟩

/-- **The displayed cokernels of Stacks 09YT are constructible**, granted the constructibility of
the summands `j_{U!}(Z/nZ)`, which is Stacks 03S8 (2) at the finite abelian groups `Z/nZ`.

Constructibility of abelian sheaves is a weak Serre condition by Stacks 03RZ (2) — the instance
`AlgebraicGeometry.Constructible.constructibleAbelianSheaf_isWeakSerreClass` — hence closed under
finite coproducts and under cokernels. -/
public theorem isConstructibleAbelianSheaf_of_zModShriekPresentation
    (P : SmallEtale B X.obj X.property → Prop)
    (hshriek : ∀ (U : SmallEtale B X.obj X.property) (n : ℕ), P U → 0 < n →
      IsConstructibleAbelianSheaf B X (abelianShriekZMod B X n U))
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : HasFiniteZModShriekPresentation B X P F) : IsConstructibleAbelianSheaf B X F := by
  have hcop := isClosedUnderFiniteCoproducts_of_isWeakSerreClass
    (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
      IsConstructibleAbelianSheaf B X G)
  obtain ⟨n, m, U, V, a, b, hU, hV, ha, hb, f, ⟨e⟩⟩ := hF
  have hsum : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.obj X.property) (c : Fin k → ℕ),
      (∀ i, P (W i)) → (∀ i, 0 < c i) →
      IsConstructibleAbelianSheaf B X (∐ fun i => abelianShriekZMod B X (c i) (W i)) :=
    fun W c hW hc => ObjectProperty.prop_coproduct _ fun i => hshriek (W i) (c i) (hW i) (hc i)
  exact ObjectProperty.prop_of_iso _ e
    (ObjectProperty.prop_cokernel _ f (hsum V b hV hb) (hsum U a hU ha))

/-- **Stacks 09YT**, the inclusion of the displayed cokernels into the constructible abelian
sheaves. Let `X` be quasi-compact and quasi-separated. Every abelian sheaf of the form
`Coker(⨁_j j_{V_j!}(Z/m_jZ) → ⨁_i j_{U_i!}(Z/n_iZ))`, with the `V_j` and `U_i` quasi-compact
quasi-separated objects of `X_étale` and the `m_j`, `n_i` positive, is a constructible abelian
sheaf, granted Stacks 03S8 (2) for the summands.

The reverse inclusion — every constructible abelian sheaf has such a presentation — is the other
half of the tag and is not proved here. The source deduces it from Stacks 095N at `Λ = Z/nZ`
together with the omitted fact that on a quasi-compact `X` every constructible abelian sheaf is
annihilated by some positive integer. Stacks 095N is now in the library, as
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_hasFiniteShriekPresentation`, but only for
sheaves of modules over a single ring in the model `Sheaf J (ModuleCat Λ)`, and three separate
things are missing for the reduction: the global annihilation statement, whose absence this
library already records in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage` as waiting on
this very tag; a comparison between abelian sheaves annihilated by `n` and sheaves of
`Z/nZ`-modules, which `CategoryTheory.Sheaf.coefficientEquivalence` cannot supply because it
needs an equivalence of coefficient categories and `AddCommGrpCat` is not equivalent to
`ModuleCat (ZMod n)`; and an identification of `AlgebraicGeometry.moduleShriekConstant` at
`Z/nZ` with `AlgebraicGeometry.abelianShriekZMod`, which is not bookkeeping — the analogous
comparison between extension by zero of modules and of the underlying abelian sheaves is *not*
an isomorphism in general, by the counterexample
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`. -/
@[stacks 09YT "the inclusion of the displayed cokernels at quasi-compact quasi-separated objects \
  into the constructible abelian sheaves, granted Stacks 03S8 (2) at the finite groups Z/nZ as \
  the hypothesis h03S8; the reverse inclusion needs Stacks 095N at Lambda = Z/nZ and is not \
  proved here"]
public theorem isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation
    (h03S8 : AbelianShriekZModIsConstructible B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) F) :
    IsConstructibleAbelianSheaf B X F :=
  isConstructibleAbelianSheaf_of_zModShriekPresentation B X _
    (fun U n hU hn => h03S8 X U n hn hXc hXq hU) hF

/-- **Stacks 09YT, the affine form of the same inclusion.** "In fact, we can even assume `U_i` and
`V_j` affine": for this inclusion that is a weakening of the hypothesis, since an affine scheme is
quasi-compact and quasi-separated, so the affine cokernels are constructible as well. -/
@[stacks 09YT "the same inclusion for the affine form of the displayed cokernels (the tag's \
  concluding sentence), granted Stacks 03S8 (2) at the finite groups Z/nZ as the hypothesis \
  h03S8"]
public theorem isConstructibleAbelianSheaf_of_affineZModShriekPresentation
    (h03S8 : AbelianShriekZModIsConstructible B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : HasFiniteZModShriekPresentation B X (SmallEtale.IsAffine B X.obj X.property) F) :
    IsConstructibleAbelianSheaf B X F :=
  isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation B X h03S8 hXc hXq
    (hasFiniteZModShriekPresentation_qcqs_of_affine B X hF)

end AlgebraicGeometry

end
