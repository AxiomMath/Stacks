module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.TensorDifferential

/-!
# The free graded module on a sheaf of graded sets is flat

Let `(C, O)` be a ringed site, let `A` be a sheaf of graded `O`-algebras and let `S` be a sheaf of
graded sets. The free graded `A`-module `A[S]` on `S` is flat: the functor `N ↦ A[S] ⊗_A N` is
exact on left graded `A`-modules. This is condition (1) of the definition of a *good* right
differential graded module, Tag 0FSA, for the module of Tag 0FSG.

The proof is the source's. For a left graded `A`-module `N` the relative tensor product
`A[S] ⊗_A N` is `N[S]`, the free graded module on `S` with coefficients in `N`, because the
summand `s · A^{p - deg s}` of `A[S]` tensored over `A` with `N` contributes `s · N^{n - deg s}`;
and `N ↦ N[S]` is exact, which gives flatness.

## Main results

* `SheafOfModules.freeGradedModule_isGradedFlat`: `A[S]` is flat as a graded `A`-module.
* `SheafOfModules.freeDGModule_isGradedFlat`: **Tag 0FSG, condition (1) of Tag 0FSA.** The graded
  module underlying the free differential graded `A`-module `A[S]` is flat.
* `SheafOfModules.freeDGModule_isKFlat`: **Tag 0FSG, condition (2) of Tag 0FSA.** The free
  differential graded `A`-module `A[S]` is K-flat.
* `SheafOfModules.freeDGModule_baseChange_id`: the clause of condition (3) of Tag 0FSA at the
  pullback datum along the identity morphism of ringed sites, which is conditions (1) and (2)
  for `A[S]` again. One instance of condition (3) and not condition (3).

## Implementation notes

Goodness is the three-condition notion of Tag 0FSA, formalized as
`SheafOfModules.DifferentialGradedModule.IsGood`: (1) flatness of the underlying graded module,
(2) K-flatness, (3) both after arbitrary base change. Conditions (1) and (2) are both proved
here, in the library's own `SheafOfModules.RelativeTensor.IsGradedFlat` and
`SheafOfModules.RelativeTensor.IsKFlat`, the first two conjuncts of `IsGood`. Neither carries
any hypotheses.

Condition (3) is **not** proved here and no part of it is claimed, so none of the three
site-indexed readings of goodness — `SheafOfModules.DifferentialGradedModule.IsGood`,
`IsGoodCocontinuousBaseChange` and `IsGoodSiteBaseChange` — is concluded here. At the source's
own reading it **is** concluded, elsewhere: `SheafOfModules.freeDGModule_isGoodToposBaseChange`
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`
is `A[S]` at `SheafOfModules.IsGoodToposBaseChange`, whose condition (3) quantifies over
morphisms of ringed topoi exactly as Tag 0FSA does, and that is where Tag 0FSG is registered.

For condition (3) at the three site readings the obstruction is structural, and it is worth
stating exactly, because the route the source takes is blocked at each of them — and at the
reading `IsGood` uses it is not merely unbuilt but false.

The source obtains condition (3) from `f^*A[S] = A'[f^{-1}S]`. Condition (3) of `IsGood` does
hand over the pullback: a `SheafOfModules.DifferentialGradedModule.PullbackData`, which pins
`f^*M` by the universal property that `φ`-semilinear maps out of `M` are morphisms of modules
out of `f^*M`, and that determines `f^*A[S]` up to unique isomorphism. What is absent is the
other side of the identification, and the means to prove it.

1. **The universal property of `A[S]` does not reach a semilinear map.** A `φ`-semilinear map
   `A[S] ⟶ N` is, by `SheafOfModules.DifferentialGradedModule.SemilinearHom`, a family of maps
   of local sections from `A[S]^i(V)` to `N^i(u V)` compatible with restriction: a morphism of
   *presheaves* on `C` from `A[S]` into `u.op ⋙ N`. Every piece of `A[S]` is a sheafification,
   and `SheafOfModules.freePiece_hom_ext` — the uniqueness half of the universal property —
   holds because its target is a *sheaf*, the map from the presentation being only locally
   surjective. So the lift and the uniqueness are available for a morphism of modules and not
   for a semilinear map, unless the semilinear map can be turned into a morphism into a sheaf.

   This development has that bridge:
   `SheafOfModules.DifferentialGradedModule.semilinearHomEquiv` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean` is the
   bijection between `φ`-semilinear maps `P ⟶ N` and morphisms `P ⟶ f_*N` into the constructed
   direct image. It carries `u.IsContinuous J J₁`, and so do `pushforwardObj` and
   `sitePushforward` beneath it — necessarily, since `u.op ⋙ N` is a `J`-sheaf precisely when
   `u` is continuous, which is what `CategoryTheory.Functor.IsContinuous` asserts. With no
   hypothesis on `u` there is no `f_*N` to map into, and a semilinear map out of `A[S]` is
   neither determined by nor assembled from the images of the canonical generators.

   The cofree differential graded module does not repair this.
   `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap` and `graded_hom_ext` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackGraded.lean` do
   reach homomorphisms of the *underlying graded* modules out of a pullback with no continuity
   hypothesis, by testing against a single cofree differential graded module — that is what
   Tag 0FSC uses to transport the splitting of an admissible short exact sequence, and the same
   argument gives uniqueness against an arbitrary graded target and not only against another
   pullback. What a cofree test object fixes is the *differential*: a homomorphism of graded
   modules `M → N` is a morphism of differential graded modules `M ⟶ Cofree.cofree N`. The gap
   above is the *sheaf condition*, and `u.op ⋙ Cofree.cofree N` is no more a `J`-sheaf than
   `u.op ⋙ N` is; the cofree module is built on the target site, so it is not a sheaf on `C`
   for `freePiece_hom_ext` to map into either.

2. **At `IsGood` the identification is false, not merely unprovable.** Condition (3) of
   `IsGood` quantifies over an arbitrary functor `u` of the underlying categories, which need
   not be a morphism of sites. Take `C₁ = C` with the trivial topology and `u` the identity.
   Every presheaf is a sheaf there, a `φ`-semilinear map is exactly a morphism of presheaves of
   modules, so the underlying presheaf of `M` with the identity unit is a `PullbackData` and
   `f^*A[S]` is `A[S]` itself. The inverse image along the identity is `S` again — for a sheaf
   of graded sets concentrated in degree `0`, at any rate, which is all this needs — and
   `A₁[f^{-1}S]` is then the *presentation* `SheafOfModules.freePres`, sheafified for the
   trivial topology, that is, not sheafified at all. The two differ already for such an `S`
   with sections over a covering of `V` and none over `V`: the presentation is `0` over `V`
   and `A[S]` is not.

3. **There is no `f^{-1}S`, and condition (3) fixes no universe one could live in.** A
   `Stacks.SheafOfGradedSets` is a sheaf of sets together with a morphism to the constant sheaf
   of integers, and this development has no operation carrying one along a functor of sites:
   the three constructions of a sheaf of graded sets it does have build one from a sheaf of
   sets, from an object of the site, or from a differential graded module, and none of them is
   functorial in a sheaf of graded sets. The piece that would build the inverse image is
   `CategoryTheory.Functor.sheafPullback u (Type w) J J₁`, left adjoint to restriction of
   sections along `u.op`, and it requires `u.IsContinuous J J₁`. The degree morphism asks for
   nothing beyond that: the inverse image of a constant sheaf carries a canonical map to the
   constant sheaf, namely the adjoint of `CategoryTheory.toSheafify` on the target site
   whiskered by `u.op`, the constant presheaf on `C` being the restriction of the constant
   presheaf on `C₁` on the nose. So
   `Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso` of
   `StacksFrontier/CategoryTheory/Sites/LocallyConstant/InverseImage.lean`, an *isomorphism* and
   accordingly carrying terminal objects of both sites and an identification of their images,
   is more than the construction needs.

   What blocks the route even where continuity is available is the universe `S₁` would have to
   live in. `SheafOfModules.freeDGModule` on `S₁ : Stacks.SheafOfGradedSets.{w₁} J₁` over
   `A₁ : DifferentialGradedAlgebra.{t, m₁}` is a `DifferentialGradedModule.{t, m₁, max w₁ m₁}`,
   and the conclusion of condition (3) is about a `DifferentialGradedModule.{t, m₁, m₁}`, so
   `w₁` must be `m₁`; and `S₁ : Stacks.SheafOfGradedSets.{m₁} J₁` needs
   `HasWeakSheafify J₁ (Type m₁)`, which is not among condition (3)'s binders and which Lean
   fails to synthesize from them.

   The reason is not the one it looks like. Mathlib does **not** supply sheafification of
   sheaves of types only at `Type (max u₁ v₁)`: the instance registered at that level in
   `Mathlib/CategoryTheory/Sites/LeftExact.lean` is an instance of a general one whose only
   real hypothesis is that the covers of the site be small in the coefficient universe, so
   `HasWeakSheafify J₁ (Type w₁)` is synthesized for every `w₁` of the form `max u₁ v₁ …`,
   `max m u v u₁ v₁` included. The constraint comes from the inverse image itself. The sheaf
   pullback is a left Kan extension along `u.op` followed by sheafification, and the Kan
   extension is a colimit over `CostructuredArrow u.op X`, whose objects pair an object of `C`
   with a morphism of `C₁`: it needs `w₁ ≥ max u v v₁`, where sheafification needs only
   `w₁ ≥ max u₁ v₁`. Concretely: `u.sheafPullback (Type w₁) J J₁` elaborates
   at `w₁ = max u v u₁ v₁` and fails at `w₁ = max u₁ v₁` and at `w₁ = max m u₁ v₁`. With `S`
   itself to accommodate the level is `max m u v u₁ v₁`.

   So the right-hand side is missing because `m₁` is a parameter condition (3) leaves free,
   while the inverse image of a sheaf on `(C, J)` genuinely lives above all four universes of
   the two sites. Fix `m₁` at `max m u v u₁ v₁` and it appears: in condition (3)'s own binder
   context at that level, with `u` continuous, the inverse image of a sheaf of graded sets is
   constructible — the sheaf pullback of the underlying sheaf, and the canonical map above for
   the degree — and the free differential graded module on it has exactly the type
   `DifferentialGradedModule.{t, m₁, m₁} A₁` the conclusion speaks about. What is then left is
   the identification itself, the half the source disposes of with "it is straightforward to
   see": that the canonical semilinear map `A[S] ⟶ A₁[f^{-1}S]` is a pullback. That is work,
   not an obstruction.

   A theorem at `m₁ = max m u v u₁ v₁` is not condition (3), though. It drops every base change
   to a site whose module universe does not contain the source's, which is part of what the
   predicate quantifies over, and the hypothesis cannot be moved onto the predicate instead,
   its universes and its instance binders both being bound inside it. None of this makes
   condition (3) false: where `m₁` is too small there may be no `PullbackData` at all, and the
   clause would hold vacuously. What is established is that the source's argument cannot be run
   at the quantification the development has.

   The same check in the binders of condition (3) of
   `SheafOfModules.DifferentialGradedModule.IsGoodSiteBaseChange`, which carries
   `u.IsContinuous J J₁`, gives the same answer and says precisely which instance is missing.
   With `u`, `σ`, `A₁`, `φ` and the pullback datum all in scope,
   `u.sheafPushforwardContinuous (Type m₁) J J₁` elaborates, so continuity does its work at the
   free universe `m₁` and the direct image is there; what fails is
   `(u.sheafPushforwardContinuous (Type m₁) J J₁).IsRightAdjoint`, and it fails still when
   `HasWeakSheafify J₁ (Type m₁)` is assumed outright, which is the second confirmation that
   sheafification is not the constraint. Adding
   `∀ F : Cᵒᵖ ⥤ Type m₁, u.op.HasLeftKanExtension F` — equivalently
   `∀ Y : C₁ᵒᵖ, Small.{m₁} (CostructuredArrow u.op Y)`, the form in which
   `StacksFrontier/CategoryTheory/Sites/Continuous.lean` states it — makes the inverse image
   elaborate, and that is the whole of the obstruction. It is a hypothesis on `u`, and
   condition (3) binds `u` inside its own `∀`, so it cannot be hoisted onto a theorem about the
   predicate. Lean reports the comma category's objects in `Type (max u v₁)` and its morphisms
   are those of `C`, so the requirement is `m₁ ≥ max u v v₁`: the smallness is automatic at
   `max m u v u₁ v₁`, and fails both at the free `m₁` and at `m₁ = m`, the instantiation the
   colimit statements of `GoodDifferentialGradedSiteColimit.lean` use.

4. **Three ways round obstruction 3, and why all three are closed** — the first of them
   correcting the reading of obstruction 1 above.

   *Can the conclusion be restated by a universal property, so that `A₁[f^{-1}S]` never has to
   be formed?* No, for two independent reasons. The conclusion of condition (3) is not an
   identification: it is `RelativeTensor.IsGradedFlat` and `RelativeTensor.IsKFlat` of
   `PD.obj P`, and both are defined **on the object**, quantifying over the relative tensor
   products `RelativeTensor.gradedTensor` and `RelativeTensor.dgTensor` assembled from its
   pieces. A characterisation pins the pullback up to isomorphism and no more, so it can only
   be used to transport flatness from another module already known to be flat, and the only
   such module is `A₁[f^{-1}S]`. The universal property is not a way round the construction;
   it is a way of needing it.

   Nor is the characterisation available, and this corrects obstruction 1. The bridge from a
   semilinear map to a morphism into a sheaf,
   `SheafOfModules.DifferentialGradedModule.semilinearHomEquiv`, takes its two modules at the
   *same* module universe — necessarily, since it lands in `P ⟶ pushforwardObj φ M`, and the
   two sides of a morphism of modules live in one universe. Condition (3) has the source
   module at `.{t, m, m}` and the pullback at `.{t, m₁, m₁}`, so with `P := A[S]` the
   equivalence does not elaborate: in the clause's own binders, Lean reports it
   expects a `DifferentialGradedModule.{t, m₁, m}` where the module on the target site is a
   `DifferentialGradedModule.{t, m₁, m₁}`. Obstruction 1 therefore does **not** dissolve at
   `IsGoodSiteBaseChange`; it dissolves only where `m₁` is `m`. The direct image itself is
   unaffected — `pushforwardObj φ N` elaborates, at `.{t, m, m₁}` — and so is the unit
   `PD.unit A[S]`, a `SemilinearHom` being a family of maps on local sections rather than a
   morphism in a category.

   *Is the clause vacuous where the inverse image is unavailable, so that it could be
   discharged by cases?* It is not vacuous, and it could not have been discharged that way in
   any case. `SheafOfModules.DifferentialGradedModule.idPullbackData` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackIdentity.lean` is a
   `PullbackData` along `𝟭 C`, with the identity structure map and the identity homomorphism
   of algebras, and it carries no hypotheses whatever: no continuity, no sheafification, no
   smallness, no relation between the module universe and the universes of the site.
   Instantiating condition (3) at `C₁ := C`, `J₁ := J`, `u := 𝟭 C`, `A₁ := A` — so at
   `m₁ = m`, `v₁ = v`, `u₁ = u` — hands over a pullback datum at every assignment of the
   universes, `m₁ < max u v v₁` included, which is precisely the range the vacuity would have
   had to cover. `SheafOfModules.freeDGModule_baseChange_id` is the clause's content there:
   conditions (1) and (2) for `A[S]` again. Before that file the development had no term of
   `PullbackData` at all, which is why the binder's inhabitation had never been tested.

   Vacuity could not have been used even if it held. `m₁`, `v₁` and `u₁` are universe
   parameters of `IsGood`, so a proof of condition (3) is one term valid at every assignment
   of them, and Lean has no case analysis on universe levels: "vacuous where `m₁` is too
   small, constructed elsewhere" is not a proof that can be written. The only expressible form
   is a *uniform* derivation of the missing instance from the pullback datum, inside the
   binders; and since the identity datum exists over an arbitrary site at an arbitrary module
   universe, such a derivation would prove `Small.{m} (CostructuredArrow (𝟭 C).op Y)`, the
   smallness of `Σ X : Cᵒᵖ, (X ⟶ Y)`, for every site — false as soon as the slice over `Y` has
   more objects than `Type m` has elements.

   *Can `f^{-1}S` be replaced by a universe lift into `m₁`?* A lift raises, and the obstruction
   is that `f^{-1}S` is too big. `CategoryTheory.uliftFunctor.{max u v u₁ v₁, m}` carries `S`
   up to the level where the sheaf pullback lives, and nothing brings the result back down.
   At the end of that route, with the sheafification instances the larger level needs
   supplied by hand: `freeDGModule S₁ A₁` for
   `S₁ : Stacks.SheafOfGradedSets.{max m u v u₁ v₁} J₁` does elaborate, and it is a
   `DifferentialGradedModule.{t, m₁, max m u v u₁ v₁ m₁} A₁` — not the
   `DifferentialGradedModule.{t, m₁, m₁} A₁` the conclusion is about, and the two cannot be
   compared at all. The failure a predecessor met in synthesizing
   `J.PreservesSheafification CategoryTheory.uliftFunctor` reproduces, as a deterministic
   timeout at 20000 heartbeats with no applicable instance — Mathlib supplies
   `PreservesSheafification` for a left adjoint and for the forgetful functor of a concrete
   category, and `uliftFunctor` on types is neither — but that is not what closes this line.
   Granted the lift, the free module would still be at the wrong universe.

The missing continuity hypothesis is not an oversight. The implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedModule.lean` record that
`CategoryTheory.Functor.IsContinuous` is deliberately *not* assumed in `IsGood`, because it
tests sheaves of types valued in one universe built from all four universes of the two sites and
so would tie them together and exclude base change to a site in another universe.
`IsGoodCocontinuousBaseChange` weakens condition (3) instead to the base changes whose pullback
preserves colimits, which does not restore the sheaf condition for `u.op ⋙ N`, and
`SheafOfModules.DifferentialGradedModule.IsGoodSiteBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedSiteColimit.lean` reads
condition (3) over the base changes along a morphism of ringed *sites*, which does restore it:
obstruction 2 does not arise there, and obstruction 1 dissolves as far as the universes let it
— only to `m₁ = m`, by the analysis in 4 above — while obstruction 3 remains. So condition
(3) is out of reach for `A[S]` at all three predicates as they stand.

`IsGoodSiteBaseChange` is the closest of the three to the source — it restricts `u` to a
continuous functor — and it is blocked at the same point as the others, by one instance,
`Small.{m₁} (CostructuredArrow u.op Y)`, which speaks about the `u` the predicate quantifies
over, and by the universe gap of item 4. What unblocks the source's argument is not a better
construction of the inverse image but a base-change datum that carries one, and the source's own
datum does: a morphism of ringed topoi carries `f⁻¹` and `f_*` as fields. Condition (3) read over
those, and nothing else, is `SheafOfModules.IsGoodToposBaseChange`, at which `A[S]` is good
unconditionally and Tag 0FSG is registered. Items 5 to 8 below explain
why.

5. **The blocker is an artefact of how condition (3) encodes the base change, and not
   mathematics.** The instance is needed only because the inverse image has to be
   *constructed* from the bare functor `u`, as a left Kan extension along `u.op` followed by
   sheafification. In condition (3)'s own binders: `u.sheafPullback (Type m₁) J J₁`
   fails to elaborate with both `u.IsContinuous J J₁` and `HasWeakSheafify J₁ (Type m₁)` in
   scope, and the goal it leaves is the instance
   `(u.sheafPushforwardContinuous (Type m₁) J J₁).IsRightAdjoint`; adding
   `∀ Y : C₁ᵒᵖ, Small.{m₁} (CostructuredArrow u.op Y)` makes it elaborate and nothing else is
   needed. That is the exact failing term and the exact goal that cannot be closed.

   The smallness is *true* wherever the source speaks, its sites being categories in one
   universe of sets, and it is un-hoistable only because `u` is bound inside condition (3)'s
   own `∀`. It says nothing about the mathematics of `A[S]`: along a morphism of topoi the
   inverse image is **data** rather than a construction. `MorphismOfTopoi` of
   `StacksFrontier/CategoryTheory/Sites/Topos/MorphismOfTopoi.lean` carries `f⁻¹` as a field, with
   the two topoi at independent universes, so the inverse image of the sheaf of sets underlying
   a `Stacks.SheafOfGradedSets.{m} J` is a sheaf on the target site with no smallness
   hypothesis and with no relation between `m` and `m₁`, in the same binders. A
   morphism of *ringed* topoi, `AlgebraicGeometry.RingedToposHom` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean`, is what the source's
   condition (3) quantifies over in the first place. So the repair is not a better construction
   of `f^{-1}S` but the source's own base-change datum.

   Obstruction 2 is an artefact of the same encoding from the other side: `IsGood` admits
   base-change data along functors which are not morphisms of topoi, and the clause at the
   trivial-topology datum, where the source's identification is false, is not part of Tag
   0FSA's condition (3) at all.

   The half of the source's third paragraph that depends on none of this is formalized.
   `SheafOfModules.freeDGModule_baseChange_of_free` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleBaseChange.lean` is the clause
   of condition (3) at any datum along which the pullback of `A[S]` is again free on a sheaf of
   graded sets, with no hypothesis on `u` and none relating the two module universes. The
   remaining gap in Tag 0FSG was the identification `f^*A[S] = A'[f^{-1}S]` at a datum which
   supplies `f^{-1}`, and it is closed: at a morphism of ringed topoi it is
   `SheafOfModules.freeDGModuleToposCorepresentableBy`, which exhibits `B[f⁻¹S]` as *the*
   pullback by its universal property rather than comparing two constructed objects.

6. **The sheaf-of-sets half of that identification is available, and it needs no functor of sites
   at all.** `Stacks.SheafOfGradedSets.inverseImage` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSetsToposInverseImage.lean` is `f^{-1}S`
   for a morphism of topoi `f`, built from the `inverseImage` field and
   `Stacks.inverseImageConstantIntegerIso`, which identifies `f^{-1}` of the constant sheaf of
   integers with the constant sheaf of integers: both are the coproduct of `ℤ` copies of the
   terminal sheaf, a left adjoint preserves that coproduct and a left exact functor preserves
   the terminal object. `Stacks.inverseImageDegreeFiberIso` carries this down to each degree —
   `f^{-1}` of the sheaf of degree-`i` local sections of `S` is the sheaf of degree-`i` local
   sections of `f^{-1}S` — which is what the grading of `A'[f^{-1}S]` is read off. There is no
   `u` in any of those statements, no smallness, and no relation between the two coefficient
   universes; this confirms the analysis of item 5 from the positive side.

7. **What is left is the module half, and the analysis names it exactly.** The source's
   argument identifies morphisms out of `f^*A[S]` with morphisms out of `A'[f^{-1}S]`, and in
   this development the chain runs:
   `(f^*A[S] ⟶ N) ≃ SemilinearHom φ (A[S]) N ≃ (A[S] ⟶ f_*N)`, then the universal property of
   `A[S]` on the source site, then the adjunction `f^{-1} ⊣ f_*` of sheaves of sets degree by
   degree, then item 6, then the universal property of `A'[f^{-1}S]`. The first step is
   `PullbackData.isPullback`. The second is
   `SheafOfModules.DifferentialGradedModule.semilinearHomEquiv` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean`, **and it
   carries `[u.IsContinuous J' J]` and one single module universe for the two sites**, because
   `f_*` there is `SheafOfModules.sitePushforward`, restriction of sections along `u`, which is
   a sheaf only when `u` is continuous and does not change the section universe. That is the
   residue: a hypothesis on `u` and the identification `m₁ = m`, neither of which
   belongs in condition (3), and both of which disappear if the direct image is *data* — a
   morphism of topoi carries `f_*` as a field, between sheaf categories at independent
   universes. The development has that for sheaves of sets and for sheaves of modules
   (`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, Tags 03D6 and 03D7) and
   **not** for sheaves of differential graded modules, which is the one missing construction.
   Three further pieces are then needed and are routine. **All three are available.** The sheaf
   of closed degree-`i` local sections is
   `SheafOfModules.DifferentialGradedModule.closedSectionSheaf` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedClosedSections.lean`, the
   subtype sheaf `Stacks.eqFiber` cut out by the differential against zero on the underlying
   sheaves of sets, with `closedSectionSheafIso` identifying it with their equalizer — the shape
   left exactness of `f_*` applies to — and `closedSectionMap` its functoriality in the module.
   The universal property restated as
   `(A[S] ⟶ Q) ≃ ∀ i, (degree-i sections of S) ⟶ (closed degree-i sections of Q)` is
   `SheafOfModules.freeDGModuleHomEquiv` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleClosedSections.lean`,
   and its naturality in `Q` is `freeDGModuleHomToClosed_comp` and
   `freeDGModuleHomEquiv_symm_comp`; `SheafOfModules.isoFreeDGModuleOfNatEquiv` turns such a
   natural bijection into the isomorphism `X ≅ A₁[S₁]` that
   `SheafOfModules.freeDGModule_baseChange_of_free` consumes, through
   `SheafOfModules.DifferentialGradedModule.isoOfNatHomEquiv`, the coYoneda lemma for right
   differential graded modules. None of those carries a hypothesis on a functor of sites, any
   smallness, or any universe identification; the only instance beyond what states them is
   `HasSheafify J (Type m)`, inherited from `Stacks.degreeFiberSheaf` and automatic at
   `Type (max u v)`.

8. **The residue is one construction, and it is available.** What stood between the pieces above
   was the direct image `f_*` of a sheaf of differential graded modules along a morphism of
   ringed topoi, needed at the second step of the chain of item 7.
   `SheafOfModules.DifferentialGradedModule.toposPushforward` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean` is it,
   built from a lax monoidal additive direct image of ordinary sheaves of modules and the
   comparison `ν` of underlying sheaves of sets; at a morphism of ringed topoi both data are
   unconditional — `ν` is the identity and the lax monoidal structure is
   `Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal` at the coherence of
   Tag 03EL, proved in `RingedToposPullbackCoherence.lean`. Nothing in it is a hypothesis on a
   functor of sites: there is no functor of sites in a morphism of ringed topoi. Nothing
   identifies the two module universes; the `m₁ = m` of item 7 and the `u.IsContinuous J J₁` of
   item 3 are both artefacts of `sitePushforward` and are absent there.

This is not the predicate-wide obstruction it once looked like. Condition (3) of `IsGood` is
discharged elsewhere in the development with no continuity at all:
`SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGood_left` and its two
siblings (Tag 0FSC,
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedAdmissible.lean`) carry
goodness, condition (3) included, across an admissible short exact sequence, on the graded
transport described above, and
`SheafOfModules.DifferentialGradedModule.isGood_pullback_of_isGood` carries it along a
pullback. What no module in this development has is condition (3) discharged outright, the
regular module `A` over itself included:
`SheafOfModules.RelativeTensor.isGradedFlat_ofDifferentialGraded_regularModule` and
`SheafOfModules.RelativeTensor.isKFlat_regularModule` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRelativeTensorUnitor.lean` carry
conditions (1) and (2) of Tag 0FSA and stop there, and the companion Tag 0FSB in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodExtensionByZero.lean` is in the same position
and sets the precedent for recording this.

Nothing is carried: both results tagged here are unconditional.

The source's `N[S]` is the existing `SheafOfModules.coeffPiece` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleCoefficients.lean`, the free graded
module on `S` with coefficients in an arbitrary graded sheaf of modules; for the pieces of a
graded algebra it **is** `A[S]`, by the definition of `SheafOfModules.freePiece`, on the nose. That
file is what lets the source's identification
`A[S] ⊗_A N = N[S]` be stated against existing objects rather than re-derived. The identification
itself is `SheafOfModules.freeTensorCoeffIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleTensor.lean`.

## References

* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w t a m z v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Tag 0FSG, condition (1) of Tag 0FSA: `A[S]` is flat as a graded module -/

section Good

variable [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)] [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {Osharp : Sheaf J CommRingCat.{t}}

/-- **The free graded module `A[S]` on a sheaf of graded sets is flat**: the functor
`N ↦ A[S] ⊗_A N` carries a short exact sequence of left graded `A`-modules to a short exact
sequence in every degree. This is condition (1) of Tag 0FSA for `A[S]`, at the level of a sheaf
of graded algebras; `SheafOfModules.freeDGModule_isGradedFlat` is the same statement for the
differential graded module `A[S]` of Tag 0FSG, and carries the tag.

The proof is the source's. Degree `n` of `A[S] ⊗_A N` is the free graded module `N[S]` on `S`
with coefficients in `N`, naturally in `N`, and `N ↦ N[S]` is exact because it is a direct sum of
shifted copies of `N` followed by sheafification. -/
theorem freeGradedModule_isGradedFlat (A : GradedAlgebra.{t, m} (toRingCat J Osharp))
    (S : SheafOfGradedSets.{m} J) :
    RelativeTensor.IsGradedFlat (freeGradedModule A S) := by
  intro N₁ N₂ N₃ f g hfg hSE n
  have hco := coeffPiece_shortExact S (fun k => f.app k) (fun k => g.app k) hfg hSE n
  have nat₁ := freeTensorCoeff_naturality A S f n
  have nat₂ := freeTensorCoeff_naturality A S g n
  have hz : RelativeTensor.gradedTensorMap (freeGradedModule A S) f n ≫
      RelativeTensor.gradedTensorMap (freeGradedModule A S) g n = 0 := by
    refine (cancel_mono (freeTensorCoeffIso A S N₃ n).hom).mp ?_
    calc (RelativeTensor.gradedTensorMap (freeGradedModule A S) f n ≫
            RelativeTensor.gradedTensorMap (freeGradedModule A S) g n) ≫
              (freeTensorCoeffIso A S N₃ n).hom
        = RelativeTensor.gradedTensorMap (freeGradedModule A S) f n ≫
            (freeTensorCoeffIso A S N₂ n).hom ≫ coeffPieceMap S (fun k => g.app k) n := by
          rw [Category.assoc, nat₂]
      _ = (freeTensorCoeffIso A S N₁ n).hom ≫
            coeffPieceMap S (fun k => f.app k) n ≫ coeffPieceMap S (fun k => g.app k) n := by
          rw [← Category.assoc, nat₁, Category.assoc]
      _ = 0 := by
          rw [coeffPieceMap_comp_eq_zero S (fun k => f.app k) (fun k => g.app k) hfg n,
            comp_zero]
      _ = 0 ≫ (freeTensorCoeffIso A S N₃ n).hom := zero_comp.symm
  refine ⟨hz, ?_⟩
  exact (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk
    (freeTensorCoeffIso A S N₁ n) (freeTensorCoeffIso A S N₂ n) (freeTensorCoeffIso A S N₃ n)
    nat₁.symm nat₂.symm)).mpr hco

/-- **Tag 0FSG, condition (1) of Tag 0FSA.** The graded module underlying the free differential
graded `A`-module `A[S]` on a sheaf of graded sets is flat. The differential plays no part: the
underlying graded module of `A[S]` as a differential graded module **is** the free graded module
on `S` over the graded algebra underlying `A`, so this is
`SheafOfModules.freeGradedModule_isGradedFlat`. -/
@[stacks 0FSG "condition (1) of good (Stacks 0FSA) for the free graded module A[S] on a sheaf \
of graded sets: the underlying graded module is flat. No hypotheses; the source's own argument. \
Condition (2) is SheafOfModules.freeDGModule_isKFlat in this file; condition (3) is not proved \
here, and goodness is concluded at SheafOfModules.freeDGModule_isGoodToposBaseChange, where \
condition (3) is read over morphisms of ringed topoi as 0FSA states it. At the three \
site-indexed readings IsGood, IsGoodCocontinuousBaseChange and IsGoodSiteBaseChange condition \
(3) is still open -- see the implementation notes"]
theorem freeDGModule_isGradedFlat (D : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp))
    (S : SheafOfGradedSets.{m} J) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (freeDGModule S D)) :=
  freeGradedModule_isGradedFlat D.toGradedAlgebra S

end Good

/-! ### Tag 0FSG, condition (2) of Tag 0FSA: `A[S]` is K-flat -/

section KFlat

variable [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)] [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {Osharp : Sheaf J CommRingCat.{t}}
  (S : SheafOfGradedSets.{m} J) (D : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp))

/-- **Tag 0FSG, condition (2) of Tag 0FSA.** The free differential graded `D`-module `D[S]` on a
sheaf of graded sets is K-flat: `D[S] ⊗_D N` is acyclic for every acyclic left differential
graded `D`-module `N`.

The proof is the source's. Degree `n` of `D[S] ⊗_D N` is the free graded module `N[S]` on `S`
with coefficients in `N`, by `SheafOfModules.freeTensorCoeffIso`, and under that identification
the differential is the signed degree-raising map of `N[S]`, by
`SheafOfModules.freeTensorCoeff_dgTensorDiff`. Exactness in degree `n + 1` is then the exactness
of a short complex of pieces of `N[S]` twisted by the sign automorphism, which
`SheafOfModules.coeffPiece_exact_sign` deduces from the exactness of `N` in the three adjacent
degrees; the transports matching the degrees of the three terms are
`SheafOfModules.coeffCastPieceIso`. -/
@[stacks 0FSG "condition (2) of good (Stacks 0FSA) for the free differential graded module D[S] \
on a sheaf of graded sets: D[S] tensor_D N is acyclic for every acyclic left differential graded \
D-module N. No hypotheses; the source's own argument. Condition (1) is \
SheafOfModules.freeDGModule_isGradedFlat in this file; condition (3) is not proved here, and \
goodness is concluded at SheafOfModules.freeDGModule_isGoodToposBaseChange, where condition (3) \
is read over morphisms of ringed topoi as 0FSA states it. At the three site-indexed readings \
IsGood, IsGoodCocontinuousBaseChange and IsGoodSiteBaseChange condition (3) is still open -- \
see the implementation notes"]
theorem freeDGModule_isKFlat : RelativeTensor.IsKFlat (freeDGModule S D) := by
  intro M hM
  have hgh : ∀ k : ℤ, gNDiff M (k - 1) k ≫ gNDiff M k (k + 1) = 0 := fun k ↦
    M.complex.d_comp_d (k - 1) k (k + 1)
  have hex : ∀ k : ℤ,
      (ShortComplex.mk (gNDiff M (k - 1) k) (gNDiff M k (k + 1)) (hgh k)).Exact := fun k ↦
    (HomologicalComplex.exactAt_iff' M.complex (k - 1) k (k + 1) (by simp) (by simp)).mp (hM k)
  have key : ∀ mm : ℤ, (RelativeTensor.dgTensor (freeDGModule S D) M).ExactAt (mm + 1) := by
    intro mm
    have hT' := coeffPiece_exact_sign S (fun k ↦ (RelativeTensor.gN M).piece (k - 1))
      (Y := (RelativeTensor.gN M).piece) (Z := fun k ↦ (RelativeTensor.gN M).piece (k + 1))
      (fun k ↦ gNDiff M (k - 1) k) (fun k ↦ gNDiff M k (k + 1)) hgh hex (mm + 1)
    rw [HomologicalComplex.exactAt_iff' _ mm (mm + 1) (mm + 1 + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN M) mm ≪≫
        coeffCastPieceIso S (RelativeTensor.gN M).piece (fun k ↦ k) (fun k ↦ k - 1) mm (mm + 1)
          (fun j ↦ by omega))
      (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN M) (mm + 1))
      (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN M) (mm + 1 + 1) ≪≫
        (coeffCastPieceIso S (RelativeTensor.gN M).piece (fun k ↦ k + 1) (fun k ↦ k) (mm + 1)
          (mm + 1 + 1) (fun j ↦ by omega)).symm)
      ?_ ?_)).mpr hT'
    · refine Eq.trans ?_ (freeTensorCoeff_dgTensorDiff S D M mm).symm
      exact (Category.assoc _ _ _).trans (congrArg
        (fun φ ↦ (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN M) mm).hom ≫ φ)
        (coeffCastPiece_coeffSignDiffPiece S (RelativeTensor.gN M).piece (gNDiff M) mm))
    · refine Eq.trans (congrArg
        (fun φ ↦ (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN M) (mm + 1)).hom ≫ φ)
        (coeffSignDiffPiece_coeffCastPiece S (RelativeTensor.gN M).piece (gNDiff M)
          (mm + 1)).symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg
        (fun φ ↦ φ ≫ coeffCastPiece S (RelativeTensor.gN M).piece (fun k ↦ k) (fun k ↦ k + 1)
          (mm + 1 + 1) (mm + 1) (fun j ↦ by omega))
        (freeTensorCoeff_dgTensorDiff S D M (mm + 1)).symm) ?_
      exact Category.assoc _ _ _
  intro n
  have hn : n - 1 + 1 = n := by omega
  exact hn ▸ key (n - 1)

/-- **Conditions (1) and (2) of Tag 0FSA for `D[S]` after the identity base change.** The
identity morphism of ringed sites carries a pullback datum,
`SheafOfModules.DifferentialGradedModule.idPullbackData`, along which every right differential
graded module is its own pullback; the clause of condition (3) at that datum is therefore
conditions (1) and (2) for `D[S]` again.

This is one instance of condition (3) and emphatically not condition (3), which quantifies over
every functor of the underlying categories. It is recorded because it is what shows the
`PullbackData` binder of that clause to be inhabited whatever the universes are, which closes
the one route to condition (3) that would not have needed the inverse image `f^{-1}S` — see the
implementation notes. -/
theorem freeDGModule_baseChange_id :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
        ((DifferentialGradedModule.idPullbackData (A := D)).obj (freeDGModule S D))) ∧
      RelativeTensor.IsKFlat
        ((DifferentialGradedModule.idPullbackData (A := D)).obj (freeDGModule S D)) :=
  ⟨freeDGModule_isGradedFlat D S, freeDGModule_isKFlat S D⟩

end KFlat

end SheafOfModules

end
