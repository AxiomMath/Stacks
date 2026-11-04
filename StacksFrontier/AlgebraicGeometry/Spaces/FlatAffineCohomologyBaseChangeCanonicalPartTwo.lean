module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeTranspose

/-!
# Stacks 073K, part (2): the chosen isomorphism is `B`-equivariant, and the two seatings compare

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine and `g` flat, part (2) of **Stacks 073K** is
registered on the chosen `B`-linear isomorphism
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`.  Turning it into
the *canonical* statement — that
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap` is invertible — is
done in
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`).  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeTranspose.lean` list the two
pieces of bookkeeping that remained; this file supplies both.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_globalSmul` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom_tmul_mul`: **the
  chosen `A`-linear isomorphism of part (2) is `B`-equivariant** — it intertwines multiplication
  by `b` on the second tensor factor with the geometric action of `b` on `H^i(X', 𝓕')`, and
  therefore sends `h ⊗ (b * c)` to `b` acting on its value at `h ⊗ c`.  The equivariance was
  already proved for
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeCoreIso`; what is new is
  that the *chosen* isomorphism — the one whose transpose is computed in
  `FlatAffineCohomologyBaseChangeTranspose.lean` — carries it too.
* `AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource_surjective`: **the comparison
  of the chart seating with the global seating of the left hand side**, `H^i(X, 𝓕) ⊗_A B ⟶
  Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} H^i(X, 𝓕)`, **and its surjectivity.**  It sends `h ⊗ b` to the
  image of `b` in `Γ(Y', 𝒪_{Y'})` acting on the unit `h ↦ 1 ⊗ h`, and it is surjective because
  the chart comparison `B ⟶ Γ(Y', 𝒪_{Y'})` is a ring *equivalence*.

## Implementation notes

*The `B`-equivariance of the chosen isomorphism is a comparison of two composites.*  It is
proved exactly as the core isomorphism's is, by composing the four commuting squares
`AlgebraicGeometry.Space.BaseChangeDiagram.spellingSquare`, `gluingSquare`,
`chartComparisonSquare` and `collapseSquare` — each stated at a *variable* target functor, which
is why they can be reused verbatim here — with the naturality of
`Stacks.FlatDevissage.tensorLeftObjIso` and of
`AlgebraicGeometry.Space.cohomologyTensorComparison`, and with one new square for the trailing
reassociation of restrictions of scalars.  Two adjustments are needed and both are cheap: the
chosen isomorphism takes the collapse in the `cohomologyPushforwardIso` form, which
`AlgebraicGeometry.Space.BaseChangeDiagram.naturalCohomologyPushforwardIso_eq` identifies with
the naturality-carrying one; and it bundles the first two steps of
`cohomologyTensorTargetIso` into
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso`, which
`pushforwardTensorChartSquare` below splits again.

*That split has to happen at the level of isomorphisms, not of their `hom`s.*  Proving
`(cohomologyFunctorOverBaseChart …).map (pushforwardTensorChartIso …).hom` equal to the
composite of the two factors' images directly — that is, asking the kernel to identify
`(pushforwardTensorChartIso …).hom` with `eqToHom … ≫ (pushforwardTensorIso …).hom` — is a
kernel timeout at the default budget.  Stating the same identification
one level up, between the two *isomorphisms*, is `rfl` in a fraction of a second, and the `hom`
equation then follows by `congrArg` and `Functor.map_comp`; the whole lemma costs 1s.

*The chart-versus-global comparison is not free.*  The
notes of `FlatAffineCohomologyBaseChangeTranspose.lean` record that the ring-map half is
`baseChartBaseRingHom_algebraMap` and suggest the module half follows because
`affineCohomologyOverBaseChart` and `affineCohomologyOverBase` have the same carrier.  They do;
but `H^i(X, 𝓕) ⊗_A B` and `Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} H^i(X, 𝓕)` are tensor products over
*different* rings, so no identity of carriers relates them and a map has to be built.  It is
built here by `TensorProduct.liftAddHom` out of the unit of extension-restriction of scalars,
which is what keeps the construction free of `Module.compHom` plumbing: every scalar action it
mentions is the one `affineCohomologySource` itself carries.

*Why the balance condition lives in its own lemma.*  Discharged inside
`chartTensorToSource`'s own tactic block — where `baseChartAlgebra` is a local instance — the
`smul_smul` step is a 200000-heartbeat `whnf` timeout; the same proof in a declaration whose
instance context does not carry that `Algebra` succeeds in under a second.  The same applies to
the rewrites: `rw` on either half of the balance condition times out while building its motive,
and the term-level `congrArg`/`Eq.trans` chain that replaces it is immediate.

*Where the two results above are consumed.*  No declaration below asserts that the canonical map
is an isomorphism; the assembly is
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`),
now proved, and this passage used to list its four steps as open.  They went exactly as
listed: the canonical map sends `s ⊗ h` to `s` acting on the pullback map's value at `h` (by
`rfl`); the chosen isomorphism sends `h ⊗ b` to the image of `b` acting on the same thing (the
equivariance above at `c = 1`, composed with `affineCohomologyBaseChangeIso_hom_tmul_one`);
hence the canonical map composed with `chartTensorToSource` *is* the chosen isomorphism, which is
bijective; and a map whose composite with a surjection is bijective is bijective.

*The inputs were not consumed through the criterion.*
`isIso_affineCohomologyBaseChangeMap_of_homEquiv_eq` asks for an isomorphism between the two
*global* seatings, and `chartTensorToSource` is only a surjection — which is why bijectivity is
proved directly there rather than by that criterion.

*Nothing here carries a `@[stacks 073K]` attribute.*  The tag has two parts, and no declaration
below states either of them; part (2) stays registered on
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` and part (1) has
no carrier.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.TensorByBaseModule hiding ringSheaf
open scoped ChangeOfRings

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u

/-- **A pure tensor in an extension of scalars depends on its left factor only through that
factor.**  Kept as a lemma because the `congrArg` it is cannot be written inline: the scalar
action on the left factor of `ModuleCat.extendScalars` is `Module.compHom _ f`, which instance
search does not produce, so the function being congruence-applied has to be given with `R`, `S`
and `f` all explicit. -/
theorem ModuleCat.extendScalars_tmul_congr_left {R : Type u} {S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) {M : ModuleCat.{u} R} {s s' : S} (h : s = s') (m : M) :
    (s ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) = s' ⊗ₜ[R, f] m :=
  congrArg (fun t => (t ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M)) h

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS) (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- **The sheaf identification `𝓕 ⊗_A B = g'_*𝓕'`, in the spelling the chosen isomorphism of
part (2) uses, is equivariant for the second tensor factor.**

`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso` is the comparison of the
two spellings of the coefficient map followed by the gluing isomorphism, and the two squares
`AlgebraicGeometry.Space.BaseChangeDiagram.spellingSquare` and `gluingSquare` are exactly their
equivariance; this composes them.  The split of the isomorphism into its two factors is taken at
the level of isomorphisms and then pushed to `hom`s by `Functor.map_comp`, which is what keeps it
cheap — see the implementation notes of this file. -/
theorem pushforwardTensorChartSquare (hg' : yoneda.relativelyRepresentable D.g'.hom)
    (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (b : baseChartRing B S hS D.Y' V₀') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          ((tensorByBaseChartModule B S hS D.f hV₀ D.F).map (D.baseModuleMul V₀ V₀' b)) ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom =
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          ((smallBaseChangeModulePushforward B S hS D.g' hg').map
            (D.pulledBackMul V₀' hV₀' b)) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have hiso : D.pushforwardTensorChartIso hg' V₀ V₀' hV₀ =
      Functor.eqToIsoObj (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
          (D.baseModule V₀ V₀') ≪≫
        D.pushforwardTensorIso hg' V₀ V₀' := rfl
  have hsplit : (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
        (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom =
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (Functor.eqToIsoObj (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
            (D.baseModule V₀ V₀')).hom ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.pushforwardTensorIso hg' V₀ V₀').hom :=
    (congrArg (fun z => (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map (Iso.hom z))
      hiso).trans ((cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map_comp _ _)
  rw [hsplit]
  exact endComm_comp
    (D.spellingSquare V₀ V₀' hV₀ (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)
    (D.gluingSquare hg' V₀ V₀' hV₀' (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)

/-- **The chosen `A`-linear isomorphism of Stacks 073K, part (2) is `B`-equivariant.**  It
intertwines the endomorphism of `H^i(X, 𝓕) ⊗_A B` induced by multiplying the second tensor
factor by `b` with the endomorphism of `H^i(X', 𝓕')` induced by the geometric action of `b` on
`𝓕'`.

This is the statement the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeTranspose.lean` describe as
"a comparison of two composites and not new mathematics": the equivariance is known for
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeCoreIso`, and the chosen
isomorphism differs from it only by the choice of collapse — now identified by
`naturalCohomologyPushforwardIso_eq` — and by the trailing reassociation of the restrictions of
scalars, whose own square is the naturality of
`AlgebraicGeometry.Space.BaseChangeDiagram.restrictScalarsSquareIso`.  Accordingly the proof is
the same chain of commuting squares, read off
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom`. -/
theorem affineCohomologyBaseChangeIso_globalSmul (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).map
          (D.baseModuleMul V₀ V₀' b) ≫
        (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom =
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom ≫
        (baseChartRestrictScalars B S hS D.Y (isTerminal_of_isIso_chart B S hS D.Y V₀)).map
          ((globalSectionsRestrictScalars B S hS D.f' ⋙
              globalSectionsRestrictScalars B S hS D.g).map
            (((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
                i).map (D.pulledBackMul V₀'
                  (isTerminal_of_isIso_chart B S hS D.Y' V₀') b))) := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  let hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
  let hV₀' : IsTerminal V₀' := isTerminal_of_isIso_chart B S hS D.Y' V₀'
  let hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  let hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  let hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
  let hXqc : IsQuasiCompactSpace B S hS D.X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS D.f.hom hY hqc
  let hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ D.f.hom
      D.X.property hY hqs
  have hS5 := D.collapseSquare V₀' hg hY hY' hV₀' i
    (globalSectionsRestrictScalars B S hS D.f ⋙ baseChartRestrictScalars B S hS D.Y hV₀) b
  rw [D.naturalCohomologyPushforwardIso_eq hg hY hY' i] at hS5
  have hS6 := Functor.map_comm (baseChartRestrictScalars B S hS D.Y hV₀)
    (D.restrictScalarsSquareIso.hom.naturality
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).map
          (D.pulledBackMul V₀' hV₀' b)))
  rw [D.affineCohomologyBaseChangeIso_hom V₀ V₀' hZ hg hqc hqs i]
  exact endComm_comp
    (tensorLeftObjIso_comm (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm
      (D.baseModuleMul V₀ V₀' b))
    (endComm_comp
      ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).naturality
        (D.baseModuleMul V₀ V₀' b))
      (endComm_comp (D.pushforwardTensorChartSquare V₀ V₀' hg' hV₀ hV₀' b i)
        (endComm_comp
          (D.chartComparisonSquare hg' V₀' hV₀'
            (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)
          (endComm_comp hS5 hS6))))

omit [IsIso V₀.obj.hom] [IsIso V₀'.obj.hom] in
/-- **The endomorphism of `H^i(X', 𝓕')` produced by that equivariance is multiplication by
`b`**, for the `B`-module structure the right hand side of part (2) carries through `f'`.

This is `AlgebraicGeometry.Space.BaseChangeDiagram.pulledBackMul_rightDerived_apply` at the
seating the chosen isomorphism lands in — the right hand side read over `A` through `f'` and then
`g`, rather than through `f` and then `g'`. -/
theorem pulledBackMul_targetOverBaseChart_apply
    [HasInjectiveResolutions (Modules.{u, u} B S hS D.X'.1 D.X'.2)]
    (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀') (i : ℕ)
    (b : baseChartRing B S hS D.Y' V₀')
    (y : (cohomologyFunctorOverBaseChart B S hS D.f' hV₀' i).obj D.pulledBack) :
    ((baseChartRestrictScalars B S hS D.Y hV₀).map
        ((globalSectionsRestrictScalars B S hS D.f' ⋙
            globalSectionsRestrictScalars B S hS D.g).map
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).map (D.pulledBackMul V₀' hV₀' b)))).hom y = b • y := by
  have key : (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).map
          (D.pulledBackMul V₀' hV₀' b)) =
      (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b) • 𝟙 _ :=
    rightDerived_globalSections_map_globalSmul B S hS D.X'
      (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b) D.pulledBack i
  exact congrArg (fun m : (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).obj
        D.pulledBack ⟶
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).obj
          D.pulledBack) => ModuleCat.Hom.hom m y) key

/-- **The chosen isomorphism of part (2), on a pure tensor whose second factor is a product.**
Its value at `h ⊗ (b * c)` is `b` acting on its value at `h ⊗ c`.

This is the element form of
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_globalSmul`, and it is
exactly the hypothesis `Stacks.FlatDevissage.baseLinearEquivOfEquivariant` asks for: together
with `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom_tmul_one` it
says that the chosen isomorphism sends `h ⊗ b` to `b` acting on the pullback map's value at
`h`. -/
theorem affineCohomologyBaseChangeIso_hom_tmul_mul (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (b c : baseChartRing B S hS D.Y' V₀')
    (x : D.affineCohomologyOverBaseChart V₀ i) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    letI : Module (baseChartRing B S hS D.Y' V₀')
        ↥(D.affineCohomologyTargetOverBaseChart V₀ i) :=
      ((baseChartRestrictScalars B S hS D.Y'
        (isTerminal_of_isIso_chart B S hS D.Y' V₀')).obj (D.affineCohomologyTarget i)).isModule
    (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
        (x ⊗ₜ[baseChartRing B S hS D.Y V₀] (b * c)) =
      b • (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
        (x ⊗ₜ[baseChartRing B S hS D.Y V₀] c) := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  exact (DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (D.affineCohomologyBaseChangeIso_globalSmul V₀ V₀' hZ hg hqc hqs i b))
      ((x ⊗ₜ[baseChartRing B S hS D.Y V₀] c :
        ↥((tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).obj
          (D.baseModule V₀ V₀'))))).trans
    (D.pulledBackMul_targetOverBaseChart_apply V₀ V₀' (isTerminal_of_isIso_chart B S hS D.Y V₀)
      (isTerminal_of_isIso_chart B S hS D.Y' V₀') i b _)

omit [IsIso V₀'.obj.hom] in
/-- **The chart comparison `B ⟶ Γ(Y', 𝒪_{Y'})` carries the `A`-action on `B` to multiplication
by the image of `A` in `Γ(Y', 𝒪_{Y'})`.**  This is
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChartBaseRingHom_algebraMap` read on a product,
the `A`-module structure of `B` being multiplication by the image of the algebra map. -/
theorem baseChartBaseRingHom_smul (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀')
    (a : baseChartRing B S hS D.Y V₀) (b : baseChartRing B S hS D.Y' V₀') :
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    baseChartBaseRingHom B S hS D.Y' hV₀' (a • b) =
      globalSectionsRingHomSite B S hS D.g (baseChartBaseRingHom B S hS D.Y hV₀ a) *
        baseChartBaseRingHom B S hS D.Y' hV₀' b := by
  let _ := baseChartAlgebra B S hS D.g V₀ V₀'
  show baseChartBaseRingHom B S hS D.Y' hV₀'
      (algebraMap (baseChartRing B S hS D.Y V₀) (baseChartRing B S hS D.Y' V₀') a * b) = _
  rw [map_mul, D.baseChartBaseRingHom_algebraMap V₀ V₀' hV₀ hV₀' a]

/-- **The unit `h ↦ 1 ⊗ h` of extension-restriction of scalars along `Γ(Y, 𝒪_Y) ⟶
Γ(Y', 𝒪_{Y'})`, at `H^i(X, 𝓕)`**, as an additive map into the left hand side of part (2).

It is packaged with its target spelled as
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologySource` so that the scalar action on
its values is the one that module carries; written inline, the unit's value has the type
`(extendScalars ρ ⋙ restrictScalars ρ).obj …` and instance search finds no
`Γ(Y', 𝒪_{Y'})`-action on it. -/
def affineCohomologySourceUnit (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    ↥(D.affineCohomologyOverBase i) →+ ↥(D.affineCohomologySource i) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS D.g)).unit.app
      (D.affineCohomologyOverBase i)).hom : _ →ₗ[_] _).toAddMonoidHom

/-- **That unit is `Γ(Y, 𝒪_Y)`-linear**, the scalars acting on the target through the comparison
`Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})` of **Stacks 0732**. -/
theorem affineCohomologySourceUnit_smul (i : ℕ)
    (t : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj)
    (x : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥(D.affineCohomologyOverBase i)) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    D.affineCohomologySourceUnit i (t • x) =
      globalSectionsRingHomSite B S hS D.g t • D.affineCohomologySourceUnit i x :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS D.g)).unit.app
      (D.affineCohomologyOverBase i)).hom.map_smul t x

omit [IsIso V₀'.obj.hom] in
/-- **The balance condition for the chart-versus-global comparison**: moving a scalar of the
coordinate ring `A` across the tensor product does not change the value of `h ⊗ b ↦ b · (1 ⊗ h)`.

Stated separately from
`AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource`, whose construction consumes it,
because the `Algebra` instance that construction carries locally turns the `smul_smul` step into
a heartbeat timeout; see the implementation notes of this file. -/
theorem baseChartSmul_affineCohomologySourceUnit (hV₀ : IsTerminal V₀)
    (hV₀' : IsTerminal V₀') (i : ℕ)
    (a : baseChartRing B S hS D.Y V₀) (b : baseChartRing B S hS D.Y' V₀')
    (x : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥(D.affineCohomologyOverBase i)) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    baseChartBaseRingHom B S hS D.Y' hV₀' b •
        D.affineCohomologySourceUnit i (baseChartBaseRingHom B S hS D.Y hV₀ a • x) =
      baseChartBaseRingHom B S hS D.Y' hV₀' (a • b) • D.affineCohomologySourceUnit i x := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  refine Eq.trans (congrArg (fun y : ↥(D.affineCohomologySource i) =>
      baseChartBaseRingHom B S hS D.Y' hV₀' b • y)
    (D.affineCohomologySourceUnit_smul i (baseChartBaseRingHom B S hS D.Y hV₀ a) x)) ?_
  refine Eq.trans (smul_smul _ _ _) ?_
  exact congrArg (fun s : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj =>
        s • D.affineCohomologySourceUnit i x)
    ((mul_comm (baseChartBaseRingHom B S hS D.Y' hV₀' b)
        (globalSectionsRingHomSite B S hS D.g
          (baseChartBaseRingHom B S hS D.Y hV₀ a))).trans
      (D.baseChartBaseRingHom_smul V₀ V₀' hV₀ hV₀' a b).symm)

/-- **The comparison of the chart seating of the left hand side of part (2) with its global
seating**: the additive map

`H^i(X, 𝓕) ⊗_A B ⟶ Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} H^i(X, 𝓕)`

sending `h ⊗ b` to the image of `b` in `Γ(Y', 𝒪_{Y'})` acting on `1 ⊗ h`.

The chosen isomorphism of part (2) is stated over the coordinate rings `A`, `B` of the two
charts, while `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap` is stated
over the global function rings; the two sides are tensor products over *different* rings, so this
map is what relates them.  It is surjective by
`AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource_surjective`, and surjectivity is
all the reduction needs. -/
def chartTensorToSource (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    ↥((tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).obj
        (D.baseModule V₀ V₀')) →+ ↥(D.affineCohomologySource i) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  letI hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
  letI hV₀' : IsTerminal V₀' := isTerminal_of_isIso_chart B S hS D.Y' V₀'
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  refine TensorProduct.liftAddHom (R := baseChartRing B S hS D.Y V₀)
    (M := ↥(D.affineCohomologyOverBaseChart V₀ i))
    (N := baseChartRing B S hS D.Y' V₀')
    { toFun := fun x =>
        { toFun := fun b =>
            baseChartBaseRingHom B S hS D.Y' hV₀' b • D.affineCohomologySourceUnit i x
          map_zero' :=
            (congrArg (· • D.affineCohomologySourceUnit i x)
              (map_zero (baseChartBaseRingHom B S hS D.Y' hV₀'))).trans (zero_smul _ _)
          map_add' := fun b₁ b₂ =>
            (congrArg (· • D.affineCohomologySourceUnit i x)
              (map_add (baseChartBaseRingHom B S hS D.Y' hV₀') b₁ b₂)).trans
                (add_smul _ _ _) }
      map_zero' := AddMonoidHom.ext fun b =>
        (congrArg (fun y : ↥(D.affineCohomologySource i) =>
            baseChartBaseRingHom B S hS D.Y' hV₀' b • y)
          (map_zero (D.affineCohomologySourceUnit i))).trans (smul_zero _)
      map_add' := fun x₁ x₂ => AddMonoidHom.ext fun b =>
        (congrArg (fun y : ↥(D.affineCohomologySource i) =>
            baseChartBaseRingHom B S hS D.Y' hV₀' b • y)
          (map_add (D.affineCohomologySourceUnit i) x₁ x₂)).trans (smul_add _ _ _) } ?_
  intro a x b
  change baseChartBaseRingHom B S hS D.Y' hV₀' b • D.affineCohomologySourceUnit i (a • x) =
    baseChartBaseRingHom B S hS D.Y' hV₀' (a • b) • D.affineCohomologySourceUnit i x
  exact D.baseChartSmul_affineCohomologySourceUnit V₀ V₀' hV₀ hV₀' i a b x

/-- **The comparison on a pure tensor.** -/
theorem chartTensorToSource_tmul (i : ℕ)
    (x : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥(D.affineCohomologyOverBase i))
    (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    D.chartTensorToSource V₀ V₀' i (x ⊗ₜ[baseChartRing B S hS D.Y V₀] b) =
      baseChartBaseRingHom B S hS D.Y'
          (isTerminal_of_isIso_chart B S hS D.Y' V₀') b •
        D.affineCohomologySourceUnit i x :=
  rfl

/-- **A scalar acting on the unit is a pure tensor**: `s · (1 ⊗ h) = s ⊗ h`. -/
theorem smul_affineCohomologySourceUnit (i : ℕ)
    (s : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj)
    (m : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥(D.affineCohomologyOverBase i)) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    s • D.affineCohomologySourceUnit i m =
      s ⊗ₜ[RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj,
        globalSectionsRingHomSite B S hS D.g] m := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  exact (ModuleCat.ExtendScalars.smul_tmul
      (M := D.affineCohomologyOverBase i) (globalSectionsRingHomSite B S hS D.g) s 1 m).trans
    (ModuleCat.extendScalars_tmul_congr_left (globalSectionsRingHomSite B S hS D.g)
      (mul_one s) m)

/-- **The chart-versus-global comparison is surjective.**  Every element of
`Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} H^i(X, 𝓕)` is a sum of pure tensors `s ⊗ h`, and `s` is the image
of a coordinate function on the chart `V₀'` because
`AlgebraicGeometry.Space.globalSectionsChartRingEquiv` is a ring *equivalence*; so `s ⊗ h` is the
value of the comparison at `h ⊗ b` for that coordinate function `b`. -/
theorem chartTensorToSource_surjective (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    Function.Surjective (D.chartTensorToSource V₀ V₀' i) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  let hV₀' : IsTerminal V₀' := isTerminal_of_isIso_chart B S hS D.Y' V₀'
  let _ := baseChartAlgebra B S hS D.g V₀ V₀'
  show Function.Surjective (D.chartTensorToSource V₀ V₀' i)
  intro w
  refine TensorProduct.induction_on
    (motive := fun w => ∃ z, D.chartTensorToSource V₀ V₀' i z = w) w ⟨0, map_zero _⟩ ?_ ?_
  · intro s m
    refine ⟨m ⊗ₜ[baseChartRing B S hS D.Y V₀]
      globalSectionsChartRingEquiv B S hS D.Y' hV₀' s, ?_⟩
    refine Eq.trans (D.chartTensorToSource_tmul V₀ V₀' i m _) ?_
    refine Eq.trans (congrArg (fun t : RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj =>
          t • D.affineCohomologySourceUnit i m)
      ((globalSectionsChartRingEquiv B S hS D.Y' hV₀').symm_apply_apply s)) ?_
    exact D.smul_affineCohomologySourceUnit i s m
  · rintro w₁ w₂ ⟨z₁, e₁⟩ ⟨z₂, e₂⟩
    exact ⟨z₁ + z₂, (map_add _ _ _).trans (congrArg₂ (· + ·) e₁ e₂)⟩

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
