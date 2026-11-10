module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCohomologySpelling
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorPullback

/-!
# The map of obstruction modules of Stacks 07YH

Clause (2) of an obstruction theory (Stacks 07YG) asks, for a morphism `(x, A) → (y, A₁)` of
objects over `S`-algebras and a semilinear map `M → N` of coefficient modules, for an induced
map of obstruction modules. For the example of Stacks 07YH that map is

```
H¹(W_A, 𝓕_A ⊗_A M) ⟶ H¹(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N),
```

the pullback map on cohomology along `g : W_{A₁} → W_A` followed by the coefficient map
`g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N`. This file constructs it, in every degree.

## Main definitions

* `Deformation.Artin.SectionsSheaf.rightDerivedRestrictScalarsIso` — restriction of scalars
  commutes with right derived functors; general, and used here twice.
* `Deformation.Artin.SectionsSheaf.obstructionMapGen` — the same map with the two base changes
  abstracted to schemes over `Spec A` resp. `Spec A₁` and over `W`, and the **base-change
  morphism of schemes as a parameter**, constrained only by the two squares the construction
  uses it through. This is the spelling in which the coherence of clause (2) is statable at an
  identity; see its own docstring and the "what is not done" below.
* `Deformation.Artin.SectionsSheaf.obstructionMap` — **the map of obstruction modules**, the
  instantiation of `obstructionMapGen` at the base-change immersion
  `baseChangeMap q (quotHom ψ t)`.

## Implementation notes

The construction is the composite of five arrows, each already available:

1. `cohomologyPlusDeltaIso` reads the source in the bounded-below spelling that the pullback
   map on cohomology is stated in;
2. `Stacks.Cohomology.moduleCohomologyPullbackMap` is that pullback map, along `g`;
3. `tensorSheafPullbackMap` is the coefficient map, applied inside `Hⁿ`;
4. `moduleCohomologyAlongIso` and `rightDerivedRestrictScalarsIso` read the result as
   restriction of scalars of `Hⁿ(W_{A₁}, -)`;
5. `restrictScalars_baseHom_compat` and `cohomologyRestrictIso` identify the resulting scalars
   with the `A`-structure on the obstruction module over `A₁`, which is what clause (2) asks
   for; the ring maps agree by `baseHomCompat`.

`rightDerivedRestrictScalarsIso` takes the additivity of its functor as an explicit argument
rather than as an instance: at `Stacks.Cohomology.moduleGlobalSections` the instance exists but
is not found, the two `Preadditive` structures involved being reached by different routes.

## What is not done

The map is constructed here. **`map_id` and `map_local` of clause (2) are proved**, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`
(`Deformation.Artin.SectionsSheaf.affineObstructionMap_id_eq` and `..affineObstructionMap_id`,
with the element-wise forms the structure's fields state their conclusions in). `map_comp` is
not, and neither is `obs_naturality`; what each still waits on is below, in the order the files
took it. `map_id` and `map_comp` of clause (2), and
`map_local`, all reduce to the behaviour of `Stacks.Cohomology.moduleCohomologyPullbackMap` under
composition of morphisms of schemes and at an identity. When this file was written that was not
available at all: the only lemma about `moduleCohomologyPullbackMap` was its naturality in the
module (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/CohomologyPullback.lean:66`),
and the cohomology map of [Stacks, Tag 01FA] it is built from has functoriality in its two *module*
arguments only — `Stacks.Cohomology.moduleCohomologyMap_comp_left` and `_comp_right`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/FunctorialityOfCohomology.lean:204`
and `:217`).

That functoriality should, however, be *derivable*, because the Leray isomorphism it would rest
on is present and unconditional: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` is [Stacks, Tag 01F5], proved twice
over, as `Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso`
(`StacksFrontier/AlgebraicGeometry/RelativeLeraySpectralSequence/Basic.lean:196`) and as
`Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesCompIso`
(`StacksFrontier/Topology/Sheaves/Cohomology/RecoveryA/DerivedDirectImageComposition.lean:346`),
with the underived input `Stacks.RelativeLeray.modulePushforward_comp` holding by `rfl`.

**The identity law is now proved.**
`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyIdentityFunctoriality` has
`Stacks.Cohomology.moduleCohomologyMap_id`: the Tag 01FA map attached to an `f`-map at
`f = 𝟙 X` is `Hⁱ(X, φ)`. Both factors of Tag 01F9 degenerate there, to the canonical comparison
`R𝟭 ≅ 𝟭` — `Stacks.Cohomology.singleRightDerivedUnit_id_app` for the Tag 01F8 factor and
`Stacks.Cohomology.DerivedPushforwardSections.compComparison_id` for the Tag 01EZ one — and
cancel. So of the three axioms, `map_id` and `map_local` no longer wait on Tag 01FA.

**The `AffineObject` glue is now built, and the previous record's description of it was wrong.**
There is no isomorphism of two pullbacks to construct: the base of the target of a morphism of
affine objects and the base change of the base of its source are *equal*, by
`Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme` (`Over.w` of the structure morphism
read through the site's inclusion, with `specMap_spec`). So
`quotOver (ψ) P.alg.toScheme = Over.mk Q.alg.toScheme` is `congrArg Over.mk` of that, and the
identity and composition laws for `baseChangeMap q (quotHom ψ t)` follow with no comparison
morphism at all — `...baseChangeMap_quotHom_affineHom_id` and `..._comp` in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsAffineObjectGlue.lean`. On top of that,
`SectionsAffineObjectMap.lean` re-indexes clauses (1) and (2) by affine objects
(`affineObstruction`, `affineObstructionMap`), which is what makes `map_id`, `map_comp` and
`map_local` statable at all; the `bot` half of the base-change data is the `top` half at the
composite base on the nose, so that re-indexing transports a *variable* and conjugates nothing.

**What `map_local` (hence `map_id`) still needs, in order.** Of the two cohomology factors of
the construction, `Stacks.Cohomology.moduleCohomologyPullbackMap_comp`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/CohomologyPullbackAdjoint.lean`)
shows they are a single Tag 01FA map,
the one attached to the `f`-map adjoint to the coefficient map, and
`...moduleCohomologyPullbackMap_comp_id` evaluates that at `f = 𝟙 X` as `Hⁱ(X, η_𝒢 ≫ k)`. Three
things are left.

1. **Done, and this is the restatement route.** The glue delivers
   `baseChangeMap q (quotHom ψ t)` as `eqToHom h'` and **not** as `𝟙`, the two fibre products
   `pullback (quotOver ψ t).hom q` and `pullback (Over.mk t).hom q` being equal objects rather
   than the same term; and generalizing the base-change morphism to a variable `g` with
   `hg : g = eqToHom h'` does not help, for a type reason and not a cost — for a variable `g`,
   `modulePushforward g` is not `𝟭`, so `η_G ≫ k` is ill-typed. Of the two cures that record
   offered, the one taken is the restatement: `obstructionMapGen` above carries the base-change
   morphism of schemes as a parameter, so the identity case instantiates it at `𝟙` on the nose,
   and `obstructionMap` is its instantiation at the immersion, with its type unchanged. No
   transport law for `moduleCohomologyMap` along an equality of ringed spaces is needed.

   The two base changes are abstracted to *opaque* schemes in `obstructionMapGen` as well, and
   that is also forced: with them spelled out as `Limits.pullback`s, checking `Hⁱ` of the ringed
   space of one of them against `Hⁱ` of an opaque scheme asks the elaborator to unfold
   `Limits.getLimitCone`, which is not exposed, and the identity case exhausts the heartbeat
   budget in `isDefEq` before any mathematics happens.
2. **Done.** The genuinely new mathematical obligation, which no earlier record names: at
   `g = 𝟙 X`,
   ```
   pullbackIdUnit X ((tensorSheafFunctor π 𝓕_X).obj M) ≫
       tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd (ofSemilinear (𝟙 A) f) =
     (tensorSheafFunctor π 𝓕_X).map f
   ```
   — that the *coefficient* half of the map, composed with the unit of the pullback–pushforward
   adjunction, is `𝓕_A ⊗_A f`. The unit does not vanish from this: `η` is not an identity,
   because `(𝟙_X)^*` is an abstract left adjoint and is not equal to `𝟭`; it is
   `Deformation.Artin.SectionsSheaf.pullbackIdUnit`. Its ingredients each need their own
   degeneration at the identity — `Stacks.RingedSpace.comparisonIso` of [Stacks, Tag 01CD], and
   inside `tildeFirstFactorMapGen` the comparisons
   `AlgebraicGeometry.Scheme.Modules.pullbackComp`, `..pullbackCongr` and
   `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`.

   **Both of its tensor factors and their assembly are now done.** The
   Tag 01CD comparison composed with the unit is the tensor product of the two units,
   `Stacks.RingedSpace.unit_comp_comparisonIso_id`, which splits the obligation into the two
   tensor factors, and each of those is now proved unconditionally:
   * the *second* is `Deformation.Artin.SectionsSheaf.unit_comp_baseChangeSheafIsoGen_id` — at
     `g = 𝟙 X` the isomorphism `g^* 𝓕_A ≅ 𝓕_{A₁}` *is* the identity law for pullback, by
     Mathlib's `pseudofunctor_right_unitality`, and the unit followed by that identity law is
     `𝟙`, by `conjugateEquiv_pullbackId_hom`;
   * the *first* is `Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id`, in
     `StacksFrontier/Deformation/Artin/Obstruction/SectionsFirstFactorIdentity.lean`, together with
     the development that file is: the two unitality laws of the pullback pseudofunctor read
     across the base-change square (`pullbackComp_congr_comp_inv_app`), the adjoint equation at
     a morphism that is *equal* to an identity but not spelled as one
     (`unit_comp_pullbackSpecIdIso`), and the comparison of [Stacks, Tag 01I9] at the identity
     ring map (`tildePullbackIso_id_hom_app`), which is built by uniqueness of left adjoints and
     so had no formula at all before.

   The assembly of the two is
   `Deformation.Artin.SectionsSheaf.unit_comp_tensorSheafPullbackMapGen_id`, in
   `StacksFrontier/Deformation/Artin/Obstruction/SectionsCoefficientIdentity.lean`:
   `tensorSheafPullbackMapGen` is the Tag 01CD comparison wrapped in the two `eqToHom`s of
   `tensorSheafFunctor_obj_eq` and followed by `Stacks.RingedSpace.tensorSheaf` applied to a
   `×ₘ` of the two factors, and carrying the unit past those `eqToHom`s and that product
   morphism is `tensorAssemble` there — every arrow a variable, the two `eqToHom`s constrained
   by `e = 𝟙` rather than inspected, so that the conclusion matches a goal written in the other
   spelling of the tensor product first-order. With it `obstructionMapGen_id`'s hypothesis is
   discharged and `..obstructionMapGen_id_of_semilinear` is unconditional.
3. **Done, including the assembly.** The four spelling comparisons the construction is wrapped
   in — `cohomologyPlusDeltaIso`, `moduleCohomologyAlongIso`, `rightDerivedRestrictScalarsIso`
   and `cohomologyRestrictIso` — do cancel at the identity. Three of them cancel against each
   other by naturality, which is `Deformation.Artin.SectionsSheaf.conjugate_map_eq`, and the
   fourth is the identity, which is
   `Deformation.Artin.SectionsSheaf.rightDerivedRestrictScalarsIso_identity_inv_app`; the whole
   cancellation in the shape the identity case has is
   `Deformation.Artin.SectionsSheaf.obstructionAssemble`. `restrictScalars (𝟙 A).hom = 𝟭`,
   `Stacks.Cohomology.restrictGlobalScalars (𝟙 X) = 𝟭` and
   `moduleCohomologyAlongIso (𝟙 X) n = spaceModuleCohomologyIso X n` all hold by `rfl`.

   Applying `obstructionAssemble` to the unfolding of `obstructionMapGen` at `g = 𝟙 X` is
   `Deformation.Artin.SectionsSheaf.obstructionMapGen_id`, and it holds granted the obligation
   of item 2. The difficulty is a definitional-equality cost, handled by splitting: the
   comparison of the two spellings of cohomology costs 8 · 10³ heartbeats between the two
   *functors*, 6.8 · 10⁴ between them applied to an object and 3.5 · 10⁶ between two morphism
   components whose codomains differ by it, so the identity case is arranged to make each
   comparison at the cheapest level available and is spread over five declarations, each
   within budget. The full account is in
   `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionIdentity.lean`.

`map_comp` needs all of that *and* the composition law for `Stacks.Cohomology.moduleCohomologyMap`
in the morphism, which is still only available for the first factor of Tag 01F9; see below.

What is missing in the composition law is still the step from the Leray isomorphism to the Tag
01FA map. Unfolding `Stacks.Cohomology.derivedGlobalSectionsMap`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/DerivedGlobalSectionsMap.lean:234`)
shows exactly which two laws are
wanted: it is `RΓ(Y, -)` applied to `Stacks.Cohomology.toDerivedPushforward` of [Stacks, Tag
01F8] followed by `Stacks.Cohomology.derivedGlobalSectionsComparison` of [Stacks, Tag 01EZ], and
each of those needs an identity law and a composition law *in the morphism*; only their
module-argument laws exist. The composition law for the second is where Tag 01F5 would enter.

**The multiplicativity of Tag 01F8 is now proved.** Writing `F` for `f_*` and `G` for `g_*`,
the composition law for `derivedGlobalSectionsMap` follows from the naturality of
`Stacks.Cohomology.singleRightDerivedUnit` in the module together with its multiplicativity in
the functor, and that is
`Stacks.Cohomology.singleRightDerivedUnit_comp_rightDerivedFunctorPlusComp_app`
(in `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/`,
file `CohomologyCompositionFunctoriality.lean`):

`(singleRightDerivedUnit (F ⋙ G)).app ℱ ≫ (rightDerivedFunctorPlusComp F G).app ℱ[0] =`
`  (singleRightDerivedUnit G).app (F.obj ℱ) ≫ RG((singleRightDerivedUnit F).app ℱ)`.

No acyclicity and no preservation of injective objects is assumed: the canonical comparison
`t : R(G ∘ F) ⟶ RF ⋙ RG` of [Stacks, Tag 05T2] exists for every additive pair, and only the
factorization `CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app` pinning it is used
— there the coherence isomorphism
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` has identity
components, by `Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_inv_comp`.
The two remaining steps are the multiplicativity of the comparisons that place a functor's
image of `ℱ[0]` against `(F ℱ)[0]`:
`HomologicalComplex.singleMapHomologicalComplex_hom_app_comp` degreewise,
`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom_comp` in the bounded below
homotopy category, and
`Stacks.Cohomology.mapSingleFunctorCompQhIso_hom_app_comp_hom_app` for
`CategoryTheory.Functor.mapSingleFunctorCompQhIso` itself.

**The transport factor is handled too.** `t` is not the comparison of [Stacks, Tag 01F5] on the
nose: `Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso` is `t` precomposed with
the transport
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso` along
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g`, whose two functors are
*equal* (`Stacks.PullbackPseudofunctor.modulePushforward_comp` holds by `rfl`), so that
transport is the identity. That is
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso_hom_eq_id`, and
the law read through it is
`Stacks.Cohomology.singleRightDerivedUnit_comp_natIsoOfIso_comp_app`.

Making that provable needed the definition
`Stacks.Cohomology.HigherDirectImagePresheaf.mapHomotopyCategoryPlusIsoOfIso` restructured, not
a lemma added around it, and the restructuring is the honest record of why. It was glued from
two `ObjectProperty.liftCompιIso` factors, each `Iso.refl _` *at a differently spelled object*
— `F.mapHomotopyCategoryPlus ⋙ Plus.ι B` against `Plus.ι A ⋙ F.mapHomotopyCategory c`,
definitionally equal and not syntactically — so a composite through them could not be taken
apart again: `CategoryTheory.Iso.trans_hom` would produce `(Iso.refl P).hom ≫ w.hom` whose two
ends are spelled differently, which is not type-correct under the `implicit` transparency level,
and `simp` declines to apply it; `Iso.refl_trans` and `Iso.trans_refl` fail to match for the
same reason. Its middle factor is now the named
`...mapHomotopyCategoryPlusCompιIsoOfIso`, a single `NatIso.ofComponents` between the two
composites with the inclusion, whose components hold by `rfl`; from that
`...ι_map_mapHomotopyCategoryPlusIsoOfIso_hom_app` is the characterizing formula — the only
handle on that `no_expose` definition, companion to
`...rightDerivedFunctorPlusNatIsoOfIso_fac_app`. The same transport is what
`...rightDerivedPlusNatIsoOfIso` and the Tag 01F5 comparison are built from, so this pays for
all of them.

The hypothesis that law asks for is about the pushforward of sheaves of modules rather than
about homological algebra, and it holds: `(pushforwardCompIso f g).hom.app ℱ = 𝟙 _` is `rfl`,
as `Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso_hom_app`
(in `StacksFrontier/Topology/Sheaves/Cohomology/RelativeMayerVietoris/`,
file `PushforwardCompIsoIdentity.lean`).

**Where the chain stops is a heartbeat cost, and it is in the instantiation and not
in the mathematics.** The three things an assembly still has to get past:

1. `pushforwardCompIso_hom_app` is `rfl` only in a file with a *small* import closure. Adding
   `Mathlib.Algebra.Homology.HomotopyCategory.Plus` to the imports of its own file is by itself
   enough to make the same `rfl` exhaust the heartbeat budget in `whnf`, which is why it has a
   file of its own and must be cited rather than restated. Its degreewise version — the literal
   hypothesis of `singleRightDerivedUnit_comp_natIsoOfIso_comp_app` — reduces to it by
   `ext i : 1` plus `exact`, and that step does go through; what then times out is closing
   `(HomotopyCategory.quotient _ _).map (𝟙 _) = 𝟙 _`, because the `𝟙` on the two sides is
   indexed at the two different spellings of the composite pushforward and matching them asks
   for the two functors to be compared definitionally.
2. Recognising `Stacks.Cohomology.singleRightDerivedUnit (modulePushforward (f ≫ g))` as
   `singleRightDerivedUnit (modulePushforward f ⋙ modulePushforward g)` goes through
   `CategoryTheory.Functor.mapSingleFunctorCompQhIso`, which is built by
   `CategoryTheory.Functor.fullyFaithfulCancelRight` and so by a `Full`-preimage; that is what
   exhausted the budget in `isDefEq` for the identity case. The cure there was to carry the
   functor as a variable with an equality hypothesis and `subst` it, and `Functor.Additive`
   being a `Prop` class is what makes the additivity instances harmless. The same cure should
   serve here. Do **not** raise the heartbeats; split the declaration.
3. Beyond the first factor, assembling the composition law for
   `Stacks.Cohomology.derivedGlobalSectionsMap` from `derivedGlobalSectionsMap_eq` still has to
   contend with the second factor, the comparison of [Stacks, Tag 01EZ], whose own composition
   law in the morphism is `Stacks.Cohomology.DerivedPushforwardSections.compIso` for three
   functors rather than two; and with the target,
   `derivedModuleGlobalSectionsAlong (f ≫ g)` against the iterated restriction of scalars,
   which agree only up to a comparison.

Note that the composition law for the comparison this file does use,
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso_comp`
(in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/`,
file `CompositeComparisonTransitivity.lean`, line 273), governs only the layers in
which an exact functor is applied after deriving — here the restrictions of scalars. It does not
reach `moduleCohomologyPullbackMap`, and so does not supply any of the three axioms.

Two facts found while probing the identity case, which is the cheapest of the three, record what
it rests on. `modulePushforward (𝟙 X) = 𝟭` and
`Stacks.Cohomology.restrictGlobalScalars (𝟙 X) = 𝟭` both hold by `rfl`, and
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology` gives that the
derived-functor unit of the identity is invertible, so the derived pushforward layer degenerates
as it should. The invertibility of
`(RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (𝟙 X)).unit` does **not**
follow and instance search does not produce it — `modulePullback (𝟙 X)` is an abstract left
adjoint and is not equal to `𝟭` — but the identity case does not need it: the unit is carried
along as `Deformation.Artin.SectionsSheaf.pullbackIdUnit` and is cancelled, not inverted, by
the adjoint equations. So `map_id` and `map_local` no longer wait on the missing functoriality
that `map_comp` waits on.

**They are not a consequence of `obstructionMapGen_id` alone — one record said they were, and
that was wrong — but the two transports that stood between them are now built**, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`.
`obstructionMapGen_id` is a statement about `obstructionMapGen` at `g = 𝟙 X`, while `map_id` and
`map_local` are statements about `Deformation.Artin.SectionsSheaf.affineObstructionMap`:

1. `obstructionMap` instantiates `g` at `baseChangeMap q (quotHom ψ t)`, and
   `Deformation.Artin.SectionsSheaf.baseChangeMap_quotHom_affineHom_id` evaluates that at an
   identity morphism of affine objects as `eqToHom h'` — a transport between two *equal* fibre
   products, not `𝟙`. Reaching `obstructionMapGen ... (𝟙 X) ...` from there needs the target
   base change, its two structure morphisms and `g` generalized to variables and the equality
   eliminated, and that is `Deformation.Artin.SectionsSheaf.obstructionMapGen_eqToHom`. Its three
   hypotheses are `∀ h : X₁ = X, …` rather than statements at a fixed proof, because the
   equality is eliminated by `subst` and a hypothesis *mentioning* the proof term would have to
   be carried along by it; that is also the form `baseChangeMap_quotHom_id` and the two
   projection transports `..pullback_fst_eqToHom`, `..pullback_snd_eqToHom` come in.
2. `affineObstructionMap` goes through
   `Deformation.Artin.SectionsSheaf.obstructionMapOf`, which carries the base of its target as
   a variable and eliminates the equality by `match`. At an identity morphism of affine objects
   that variable is instantiated at `t` while the equality reads
   `Spec.map (𝟙 A) ≫ t = t`, whose two sides are not a variable and a term, so the `match` does
   not reduce and the map is a transport of `obstructionMap` along it. What that transport is, is
   `Deformation.Artin.SectionsSheaf.obstructionMapOf_eq_comp_eqToHom`.

The two transports are inverse to each other and cancel —
`Deformation.Artin.SectionsSheaf.obstructionMapOf_id_eq` — and with item 2's coefficient
identity discharging `obstructionMapGen_id`'s hypothesis, `map_id` and `map_local` follow:
`..affineObstructionMap_id_eq` and `..affineObstructionMap_id`, with
`..affineObstructionMap_id_eq_apply` and `..affineObstructionMap_id_apply` the element-wise
forms the two fields state their conclusions in. The witnesses the two existentials ask for are
`φ := f` and `φ := 𝟙 M`: at an identity morphism of affine objects the ring map is `RingHom.id`,
so `ModuleCat.restrictScalars` of it is the identity functor on the nose and the semilinear
datum of the `map` field *is* a morphism of `Mod_A`.

`map_comp` is still not proved, and what it waits on is unchanged: the composition law for
`Stacks.Cohomology.moduleCohomologyMap` in the morphism, together with the two obstacles listed
above it.

`obs_naturality` needs that functoriality and, in addition, the compatibility of the connecting
morphisms of
`cohomologyDeltaFunctor` with the comparison of cohomology upstairs and downstairs. For abelian
sheaves that compatibility exists — `Stacks.Cohomology.AbelianColimit.H'spacePullback_comp_H'δ`
(in `StacksFrontier/Topology/Sheaves/Cohomology/SpectralSpaceLimit/`, file
`PullbackAsAMorphismOfDeltaFunctors.lean`, line 538) is exactly δ-naturality along a
continuous map — and for module cohomology it now exists along the *direct* image, needing only
that the pushforward be exact: `Stacks.Cohomology.ModulePushforwardDelta`, instantiated at the
base-change immersion as
`Deformation.Artin.SectionsSheaf.baseChangeCohomologyComparison_comp_δ`
(`SectionsThickeningDelta.lean`).

**That route is not available inside `obstructionMap`, and the reason is not a cost.**
Substituting `Stacks.Cohomology.ModulePushforwardDelta.comparison` for
`moduleCohomologyPullbackMap` in the second factor below needs `i_*` to be exact, and at the
morphism this file uses instance search reports
```
failed to synthesize instance of type class
  PreservesFiniteColimits (modulePushforward (… (baseChangeMap q (quotHom ψ t))))
```
`obstructionMap` is clause (2) for an *arbitrary* ring map `ψ : A → A₁`, and `Spec ψ` is a closed
immersion only when `ψ` is surjective; the substitution is therefore available only after adding
`IsClosedImmersion (baseChangeMap q (quotHom ψ t))` as a hypothesis, which would weaken clause
(2). The thickening of this development is the other morphism — the one a deformation situation
produces — and that is where the δ-compatible comparison is proved, at full strength.

What is still missing for `obs_naturality` is accordingly not the δ-naturality of a comparison
along a thickening, but the δ-naturality of the Tag 01FA map along a general morphism of ringed
spaces: there is still no `DeltaFunctor.Hom` built from one. Note also that
`baseChangeCohomologyComparison` is not proved to agree with `moduleCohomologyPullbackMap`, nor
with `baseChangeCohomologyIso`; those identifications are separate statements.

**`baseChangeCohomologyComparison_comp_δ` is not an input to `obs_naturality` at all, and this
is the third independent reason.** Two were already recorded: the δ-naturality it supplies is
along the base-change immersion, whereas a morphism of deformation situations relates the two
sheaf-level sequences along the morphism `W_{A₁'} → W_{A'}` that `m.top : A' → A₁'` induces,
which is an arbitrary morphism of schemes; and the substitution inside `obstructionMap` would
weaken clause (2). The third is that the comparison cannot be applied to the sheaf-level
sequence even at the immersion: its hypothesis is a short exact sequence of modules on `W_A`,
compared through its direct image, and the sequence of clause (2) is a sequence on `W_{A'}`
whose middle term `𝓕_{A'}` is not a direct image along `i` — if it were, the reduction map
`Deformation.Artin.SectionsSheaf.reductionMap` would be an isomorphism, while its kernel is
`𝓕_{A'} ⊗_{A'} I`. The argument is in the "what is not claimed" of
`SectionsThickeningDelta.lean`. What the immersion contributes to this development is the
identification of the two *outer* terms as direct images, which is an identification of single
objects and needs no δ-compatibility; `obstructionBaseChangeIso` makes it through
`baseChangeCohomologyObjIso`.

The δ-naturality that *is* available along an arbitrary map,
`Stacks.Cohomology.ModuleSpacePullback.deltaHom`, does not serve either, and its own module
docstring explains why in the form of two negative results: its target is the cohomology of
*abelian* sheaves on the source space, because to state module cohomology over an open as a
δ-functor on `Mod(R)` one must precompose with an exact functor `Mod(R) ⥤ Mod(R')`, and the one
attached to a morphism of ringed spaces — the module pullback — is exact only for a flat
morphism (Stacks 01AJ (2)), which the morphisms here are not. Nor is `deltaHom` identified with
`Stacks.Cohomology.moduleCohomologyPullbackMap`, which is the map `obstructionMap` is built from.

**Condition (iii), `hasLift_iff_obs_eq_zero`, is also not a composition of the two proved
halves**, and what separates them is now one equation of morphisms of sheaves rather than a
vague "identification". `Deformation.Artin.SectionsSheaf.hasLift_iff_exists_section` is about
the image of the restriction map of the functor `F`, and
`..exists_section_iff_obstructionClass_eq_zero` about the image of the map that `A' → A`
induces on `𝓕_{A'} ⊗_{A'} -`; the first of these maps *is* the canonical reduction
`𝓕_{A'} ⟶ i_* 𝓕_A` on global sections, by
`Deformation.Artin.SectionsSheaf.sectionsPresheafOver_map_quotHom` (and by `rfl`), and what is
missing is the identification of that reduction with the third map of the sheaf-level sequence.
`Deformation.Artin.SectionsSheaf.reductionMapGen_eq_iff` reduces it to an equality of morphisms
`i^* 𝓕_{A'} ⟶ 𝓕_A`, one side of which is `baseChangeSheafIso` and the other of which is built
from [Stacks, Tag 01CD], the counit of the immersion, [Stacks, Tag 01I9] and [Stacks, Tag 02KG];
see `StacksFrontier/Deformation/Artin/Obstruction/SectionsReductionMap.lean`. Note that the
identification is needed not only to compose the two halves but to *state* the field: the
element `obs` is applied to is a section of `𝓕_A`, while `obstructionClass` consumes a section
of `𝓕_{A'} ⊗_{A'} A`.

Accordingly no `Deformation.Artin.ObstructionTheory` is assembled.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Restriction of scalars commutes with right derived functors**: it is exact, so deriving
and then restricting is deriving the composite. -/
def rightDerivedRestrictScalarsIso {B : Type*} [Category B] [Abelian B]
    [HasInjectiveResolutions B] {R₁ R₂ : Type u} [Ring R₁] [Ring R₂] (h : R₁ →+* R₂)
    (F : B ⥤ ModuleCat.{u} R₂) (hF : F.Additive) (n : ℕ) :
    F.rightDerived n ⋙ ModuleCat.restrictScalars h ≅
      (F ⋙ ModuleCat.restrictScalars h).rightDerived n :=
  haveI := hF
  have h1 : (ModuleCat.restrictScalars.{u} h).Additive := ⟨by intros; rfl⟩
  have h2 : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} h) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have h3 : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} h) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have h4 : (ModuleCat.restrictScalars.{u} h).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F
    (ModuleCat.restrictScalars.{u} h) (F ⋙ ModuleCat.restrictScalars.{u} h) (Iso.refl _) n

/-! ### The map of obstruction modules with the base-change morphism of schemes as a parameter -/

section ObstructionMapGen

variable {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) {W X X₁ : Scheme.{u}} (π : X ⟶ Spec A)
  (s : X ⟶ W) (π₁ : X₁ ⟶ Spec A₁) (s₁ : X₁ ⟶ W) (𝓕 : W.Modules) (g : X₁ ⟶ X)

/-- **The base scalars are compatible with a morphism over `Spec ψ`**: the two composites
`A → Γ(X, 𝒪) → Γ(X₁, 𝒪)` and `A → A₁ → Γ(X₁, 𝒪)` agree. This is
`Deformation.Artin.SectionsSheaf.baseHomCompat` with the two base changes abstracted to schemes
over `Spec A` resp. `Spec A₁` and the base-change immersion to a morphism of schemes making the
square over `Spec A` commute. -/
theorem baseHomCompatGen (hfst : g ≫ π = π₁ ≫ Spec.map ψ) :
    (((Scheme.ΓSpecIso A).inv ≫ π.appTop) ≫ g.appTop) =
      ψ ≫ ((Scheme.ΓSpecIso A₁).inv ≫ π₁.appTop) := by
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, hfst, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- Restricting scalars to `A` through `Γ(X, 𝒪)` and then along `g` is restricting them through
`A₁`. -/
theorem restrictScalars_baseHomGen_compat (hfst : g ≫ π = π₁ ≫ Spec.map ψ)
    (N : ModuleCat.{u} ↑Γ(X₁, ⊤)) :
    (ModuleCat.restrictScalars (baseHom π)).obj
        ((ModuleCat.restrictScalars g.appTop.hom).obj N) =
      (ModuleCat.restrictScalars ψ.hom).obj
        ((ModuleCat.restrictScalars (baseHom π₁)).obj N) := by
  have hf : RingHom.comp (g.appTop.hom) (baseHom π) = RingHom.comp (baseHom π₁) ψ.hom := by
    ext x
    exact congrArg (fun m => CommRingCat.Hom.hom m x) (baseHomCompatGen ψ π π₁ g hfst)
  exact congrArg (fun f => (ModuleCat.restrictScalars f).obj N) hf

/-- **The map of obstruction modules of clause (2) of Stacks 07YG, with the base-change
morphism of schemes as a parameter.** For a morphism `g : X₁ → X` of the two base changes making
the square over `Spec A` and the triangle over `W` commute — the two hypotheses, and all the
construction uses of the base-change immersion — this is
```
Hⁿ(X, 𝓕_X ⊗_A M) ⟶ Hⁿ(X₁, 𝓕_{X₁} ⊗_{A₁} N),
```
the pullback map on cohomology along `g` followed by `tensorSheafPullbackMapGen`.

Carrying `g` as a parameter is what makes `map_id` and `map_local` of clause (2) *statable* at
an identity morphism of affine objects: there the base-change immersion is the transport
`eqToHom` of an equality of fibre products and not `𝟙`, and for a morphism that is not `𝟙` the
pushforward is not `𝟭`, so the degeneration of [Stacks, Tag 01FA] that
`Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id` supplies cannot be written down at all.
With `g` a parameter the identity case of *this* map is an instantiation at `𝟙`, which is
`Deformation.Artin.SectionsSheaf.obstructionMapGen_id` — unconditionally, as
`..obstructionMapGen_id_of_semilinear`. The transport from there back to `obstructionMap`, where
`g` is the immersion `eqToHom h'`, is `Deformation.Artin.SectionsSheaf.obstructionMapGen_eqToHom`
in `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`. See item 1 of the
"what is not done"
above.

Abstracting the two fibre products to opaque schemes is not cosmetic either: with them spelled
out, checking `Hⁱ(X, -)` against `Hⁱ` of the ringed space of a `Limits.pullback` asks the
elaborator to unfold `Limits.getLimitCone`, which is not exposed, and the identity case
exhausts the heartbeat budget in `isDefEq`. -/
def obstructionMapGen (hfst : g ≫ π = π₁ ≫ Spec.map ψ) (hsnd : g ≫ s = s₁) (n : ℕ)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    ((cohomologyDeltaFunctor π).functor n).obj
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        (((cohomologyDeltaFunctor π₁).functor n).obj
          ((tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N)) :=
  ((cohomologyPlusDeltaIso π n).app
      ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M)).inv ≫
    (ModuleCat.restrictScalars (baseHom π)).map
      (Stacks.Cohomology.moduleCohomologyPullbackMap g.toLRSHom.toShHom (n : ℤ)
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        (Stacks.Cohomology.moduleCohomologyAlong g.toLRSHom.toShHom (n : ℤ)).map
          (tensorSheafPullbackMapGen ψ π s π₁ s₁ 𝓕 g hfst hsnd α) ≫
        (moduleCohomologyAlongIso g n).hom.app
          ((tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N) ≫
        (rightDerivedRestrictScalarsIso
            (Stacks.Cohomology.globalSectionsRingHom g.toLRSHom.toShHom).hom
          (Stacks.Cohomology.moduleGlobalSections X₁.toRingedSpace)
          (Stacks.Cohomology.moduleGlobalSections_additive _) n).inv.app
          ((tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N)) ≫
    eqToHom (restrictScalars_baseHomGen_compat ψ π π₁ g hfst _) ≫
    (ModuleCat.restrictScalars ψ.hom).map
      ((cohomologyRestrictIso π₁ n).hom.app
        ((tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N))

end ObstructionMapGen

section ObstructionMap

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **The map of obstruction modules of clause (2) of Stacks 07YG**, for the example of Stacks
07YH: a ring map `ψ : A → A₁` over `S` and a map `A₁ ⊗_A M → N` — equivalently a semilinear map
`M → N` along `ψ`, by `ofSemilinear` — induce
```
Hⁿ(W_A, 𝓕_A ⊗_A M) ⟶ Hⁿ(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N),
```
the target carrying its `A`-module structure by restriction of scalars along `ψ`, as clause (2)
requires. It is the pullback map on cohomology along `g : W_{A₁} → W_A` followed by the
coefficient map `tensorSheafPullbackMap`.

This is the map. Its identity law is proved — `map_id` and `map_local` of clause (2), in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean` — while `map_comp` and
`obs_naturality` are not, for the reasons recorded in the module's "what is not done". -/
def obstructionMap (n : ℕ) {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    ((cohomologyDeltaFunctor (topProj t q)).functor n).obj
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj M) ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        (((cohomologyDeltaFunctor (botProj ψ t q)).functor n).obj
          ((tensorSheafFunctor (botProj ψ t q) (botSheaf ψ t q 𝓕)).obj N)) :=
  obstructionMapGen ψ (topProj t q) (pullback.snd (Over.mk t).hom q) (botProj ψ t q)
    (pullback.snd (quotOver ψ t).hom q) 𝓕 (baseChangeMap q (quotHom ψ t)) (commSqBase ψ t q)
    (baseChangeMap_comp_snd q (quotHom ψ t)) n α

end ObstructionMap

end Deformation.Artin.SectionsSheaf

end
