module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative

/-!
# Base change for the right adjoint of pushforward along a closed immersion

Let

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

be a square of ringed spaces with `i` and `i'` closed quotient morphisms, and let
`Lf^* : D(𝒪_X) ⥤ D(𝒪_{X'})` and `Lg^* : D(𝒪_Z) ⥤ D(𝒪_{Z'})` be derived pullback functors.
Tor independence of `Z` and `X'` over `X` gives an identification
`Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` ([Stacks, Tag 0E23]); granted it, the map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

of [Stacks, Tag 0E2K] is the transpose, under the derived adjunction `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)`
of [Stacks, Tag 0A76], of that identification followed by `Lf^*` of the counit
`Ri_* R ℰom(𝒪_Z, K) ⟶ K`.

[Stacks, Tag 0E2L] says that this map is an isomorphism if and only if the base change map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`

is one. Pushforward along a closed quotient morphism is exact and fully faithful, so `Ri'_*`
reflects isomorphisms, and the two sides of the map of [Stacks, Tag 0E2K] become, after `Ri'_*`,
the two sides of the base change map, by [Stacks, Tag 0E23] and [Stacks, Tag 0A77].

All names below live in the namespace `RingedSpaceModuleAdjunction.ClosedQuotientBaseChange`.

## Main definitions

* `rightAdjointBaseChangeMap` is the map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of
  [Stacks, Tag 0E2K].
* `pushforwardSourceIso` and `pushforwardTargetIso` identify the pushforwards along `i'` of its
  source and target with `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K)` and
  `R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`.
* `derivedSheafHomBaseChangeMap` is the resulting map
  `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`.

## Main results

* `map_rightAdjointBaseChangeMap`: the pushforward along `i'` of the map of [Stacks, Tag 0E2K]
  is `derivedSheafHomBaseChangeMap` read through those two identifications.
* `isIso_rightAdjointBaseChangeMap_iff_of_eq` is [Stacks, Tag 0E2L]: the map of
  [Stacks, Tag 0E2K] is an isomorphism if and only if any map filling that square is, and
  `isIso_rightAdjointBaseChangeMap_iff` is the case of `derivedSheafHomBaseChangeMap` itself.
* `isIso_rightAdjointBaseChangeMap_iff_isIso_map`: the map of [Stacks, Tag 0E2K] is an
  isomorphism exactly when its pushforward along `i'` is.

## Implementation notes

`R SheafHom_{𝒪_X}(𝒪_Z, K)` is read as the right derived functor of the internal Hom from the
ring sheaf `i_* 𝒪_Z`, which is the model [Stacks, Tag 0A77] is stated at in
`derivedModulePushforwardDerivedSheafHomExactSupportIso`; `𝒪_Z` in the displayed formulas always
means `i_* 𝒪_Z`, as in the source.

The commutativity and cartesianness of the square, and the Tor independence of `Z` and `X'` over
`X`, enter only through the isomorphism `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of [Stacks, Tag 0E23],
which is carried here as a named hypothesis `e`: [Stacks, Tag 0E23] is not proved in this
repository, and the construction of [Stacks, Tag 0E2K] cannot be written without it. For the
same reason `Lf^*` and `Lg^*` are arbitrary functors rather than the derived pullbacks: nothing
below uses any property of them.

The source identifies the base change map above with the one of Cohomology,
Remark [Stacks, Tag 08I3], and omits the verification. That verification is therefore what
`isIso_rightAdjointBaseChangeMap_iff_of_eq` takes as its hypothesis `hψ`: a consumer who
supplies it for the map of [Stacks, Tag 08I3] obtains [Stacks, Tag 0E2L] in the form the source
states it.

## References

* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientBaseChange

variable (S S' : ClosedQuotientMorphismOfRingedSpaces.{u})
  (Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.X)))
  (Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.Z)))
  (e : Lg ⋙ (modulePushforward S'.i).mapDerivedCategory ≅
    (modulePushforward S.i).mapDerivedCategory ⋙ Lf)

/-! ### The map of Stacks 0E2K -/

/-- The construction of the base change map of [Stacks, Tag 0E2K], for an arbitrary
identification `e`:
`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` for the right adjoint of pushforward along a
closed quotient morphism: the transpose, under the derived adjunction
`Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of [Stacks, Tag 0A76], of the identification `e` of
[Stacks, Tag 0E23] followed by `Lf^*` of the counit `Ri_* R ℰom(𝒪_Z, K) ⟶ K`. -/
def rightAdjointBaseChangeMap (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    Lg.obj (S.derivedSheafHomExactSupport.obj K) ⟶
      S'.derivedSheafHomExactSupport.obj (Lf.obj K) :=
  (S'.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
    (e.hom.app (S.derivedSheafHomExactSupport.obj K) ≫
      Lf.map (S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K))

/-! ### The two sides after pushforward -/

/-- The pushforward along `i'` of `Lg^* R ℰom(𝒪_Z, K)` is `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K)`: the
identification `e` of [Stacks, Tag 0E23] followed by `Lf^*` of the one of
[Stacks, Tag 0A77]. -/
def pushforwardSourceIso (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S'.i).mapDerivedCategory.obj
        (Lg.obj (S.derivedSheafHomExactSupport.obj K)) ≅
      Lf.obj (S.derivedHomSheafFromPushforwardStructureSheaf.obj K) :=
  e.app (S.derivedSheafHomExactSupport.obj K) ≪≫
    Lf.mapIso (S.derivedModulePushforwardDerivedSheafHomExactSupportIso.app K)

/-- The pushforward along `i'` of `R ℰom(𝒪_{Z'}, Lf^*K)` is
`R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`, by [Stacks, Tag 0A77] for `i'`. -/
def pushforwardTargetIso (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S'.i).mapDerivedCategory.obj
        (S'.derivedSheafHomExactSupport.obj (Lf.obj K)) ≅
      S'.derivedHomSheafFromPushforwardStructureSheaf.obj (Lf.obj K) :=
  S'.derivedModulePushforwardDerivedSheafHomExactSupportIso.app (Lf.obj K)

/-- The base change map `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`
induced by the map of [Stacks, Tag 0E2K]: its pushforward along `i'`, read through the two
identifications of [Stacks, Tag 0A77]. -/
def derivedSheafHomBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    Lf.obj (S.derivedHomSheafFromPushforwardStructureSheaf.obj K) ⟶
      S'.derivedHomSheafFromPushforwardStructureSheaf.obj (Lf.obj K) :=
  (pushforwardSourceIso S S' Lf Lg e K).inv ≫
    (modulePushforward S'.i).mapDerivedCategory.map
        (rightAdjointBaseChangeMap S S' Lf Lg e K) ≫
      (pushforwardTargetIso S S' Lf K).hom

/-- `derivedSheafHomBaseChangeMap` is the pushforward of the map of [Stacks, Tag 0E2K]
conjugated by the two identifications. -/
theorem derivedSheafHomBaseChangeMap_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    derivedSheafHomBaseChangeMap S S' Lf Lg e K =
      (pushforwardSourceIso S S' Lf Lg e K).inv ≫
        (modulePushforward S'.i).mapDerivedCategory.map
            (rightAdjointBaseChangeMap S S' Lf Lg e K) ≫
          (pushforwardTargetIso S S' Lf K).hom :=
  rfl

/-- The pushforward along `i'` of the map of [Stacks, Tag 0E2K] is the base change map
`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`, read through the two
identifications of [Stacks, Tag 0A77]. -/
theorem map_rightAdjointBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward S'.i).mapDerivedCategory.map
        (rightAdjointBaseChangeMap S S' Lf Lg e K) =
      (pushforwardSourceIso S S' Lf Lg e K).hom ≫
        derivedSheafHomBaseChangeMap S S' Lf Lg e K ≫
          (pushforwardTargetIso S S' Lf K).inv := by
  rw [derivedSheafHomBaseChangeMap_eq]
  simp

/-! ### Stacks 0E2L -/

/-- The map of [Stacks, Tag 0E2K] is an isomorphism exactly when its pushforward along `i'` is:
pushforward along a closed quotient morphism of ringed spaces is exact and fully faithful, so
`Ri'_*` reflects isomorphisms. -/
theorem isIso_rightAdjointBaseChangeMap_iff_isIso_map
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso (rightAdjointBaseChangeMap S S' Lf Lg e K) ↔
      IsIso ((modulePushforward S'.i).mapDerivedCategory.map
        (rightAdjointBaseChangeMap S S' Lf Lg e K)) := by
  refine ⟨fun _ => inferInstance, fun _ => ?_⟩
  exact isIso_of_reflects_iso _ (modulePushforward S'.i).mapDerivedCategory

/-- **Stacks Project, Tag 0E2L.** The map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of
[Stacks, Tag 0E2K] is an isomorphism if and only if a base change map
`ψ : Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)` whose pushforward
square it fills is an isomorphism.

Both directions: `Ri'_*` carries isomorphisms to isomorphisms, and it reflects them, being
exact and fully faithful. -/
@[stacks 0E2L "both directions, for a base change map filling the pushforward square; its \
  identification with the map of Cohomology, Remark 08I3, which the source omits, is the \
  hypothesis `hψ`, and the base change isomorphism `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of Stacks 0E23 \
  is the named hypothesis `e`"]
theorem isIso_rightAdjointBaseChangeMap_iff_of_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (ψ : Lf.obj (S.derivedHomSheafFromPushforwardStructureSheaf.obj K) ⟶
      S'.derivedHomSheafFromPushforwardStructureSheaf.obj (Lf.obj K))
    (hψ : (modulePushforward S'.i).mapDerivedCategory.map
        (rightAdjointBaseChangeMap S S' Lf Lg e K) =
      (pushforwardSourceIso S S' Lf Lg e K).hom ≫ ψ ≫
        (pushforwardTargetIso S S' Lf K).inv) :
    IsIso (rightAdjointBaseChangeMap S S' Lf Lg e K) ↔ IsIso ψ := by
  rw [isIso_rightAdjointBaseChangeMap_iff_isIso_map, hψ]
  simp

/-- **Stacks Project, Tag 0E2L.** The map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of
[Stacks, Tag 0E2K] is an isomorphism if and only if the base change map
`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)` it induces is an
isomorphism. -/
@[stacks 0E2L "both directions, for the base change map induced by Stacks 0E2K; the base \
  change isomorphism `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of Stacks 0E23 is the named hypothesis `e`"]
theorem isIso_rightAdjointBaseChangeMap_iff
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso (rightAdjointBaseChangeMap S S' Lf Lg e K) ↔
      IsIso (derivedSheafHomBaseChangeMap S S' Lf Lg e K) :=
  isIso_rightAdjointBaseChangeMap_iff_of_eq S S' Lf Lg e K _
    (map_rightAdjointBaseChangeMap S S' Lf Lg e K)

end RingedSpaceModuleAdjunction.ClosedQuotientBaseChange

end
