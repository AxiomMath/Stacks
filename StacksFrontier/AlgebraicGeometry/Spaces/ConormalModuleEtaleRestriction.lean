module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal module commutes with étale base change

Let `φ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `Z ⊆ X` be a closed subspace, with inclusion `i : Z ⟶ X`.  The inverse
image `Z_U = U ×_X Z = φ⁻¹(Z)` is a closed subspace of `U`, with inclusion `i_U : Z_U ⟶ U`, and
the projection `p : Z_U ⟶ Z` completes the commutative square `i_U ≫ φ = p ≫ i`.  This file
proves the conormal-module clause of Stacks 04CO:

`𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.

The functoriality in the étale source `U`, which Stacks 04CO also asserts, is **proved** — and
not here.  It is `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsConormalAction.lean`, which carries
the tag of this clause there.  That module is strictly downstream of this one — it reaches this
file through `ConormalModuleBaseChange`, `ConormalModuleBaseChangeEpi` and
`ConormalModuleBaseChangeFlat` — and the route it takes needs both the identification of the
canonical map of Stacks 04CP with the isomorphism built here and the composition law of
Stacks 04G2, so no module this file may import carries it.  The two-step morphism
`AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` defined below is *not* the vehicle for
that clause and cannot be made into one; "What is not proved" records the measurement.

The identification is the composite of three steps, each of which is already available.  The
conormal module is by definition the inverse image of the defining ideal sheaf along the
inclusion, so `p^*𝒞_{Z/X} = p^*i^*𝓘_Z`; the square identifies `p^*i^*` with `i_U^*φ^*`; along the
étale morphism `φ` the inverse image of modules is étale restriction (Stacks 03LW); and the étale
restriction of `𝓘_Z` is `𝓘_{Z_U}` on the nose, which is the ideal-sheaf clause of Stacks 04CO.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`: **Stacks 04CO** for the conormal
  module, the canonical isomorphism `p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.
* `AlgebraicGeometry.Space.conormalEtaleRestrictionSquareApp`,
  `AlgebraicGeometry.Space.conormalEtaleRestrictionPullbackComparison` and
  `AlgebraicGeometry.Space.conormalEtaleRestrictionIdealIso`: its three steps, each a named
  definition rather than a `let`-binding, so that the forward map of the composite can be
  described.
* `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`: for a further étale `ψ : V ⟶ U`,
  the two-step restriction `r^*𝒞_{Z/X} ⟶ 𝒞_{Z_V/V}`, written at the type the one-step
  identification along `ψ ≫ φ` carries.  **It has no consumer and can have none**: nothing can be
  proved about it, because no theorem statement can reproduce its body; the eleventh measurement
  under "What is not proved" says why, and the functoriality clause is stated downstream with the
  two-step composite written out instead of quoting this definition.

## Main results

* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom`: the characterising equation
  of the isomorphism — its forward map written out in terms that pre-exist it.
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom_eq` and the `_eq`/`_hom` pair
  of each step: the same, factored, so that a consumer may rewrite one step at a time.
* `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`: the commutative square
  `i_U ≫ φ = p ≫ i` of the inverse image of a closed subspace, which is the input the
  functoriality of the conormal module of Stacks 04CP consumes.
* `AlgebraicGeometry.Space.modulePullbackIdealSheafRestriction_comp`: **the fibre over the lower
  space of the functoriality of Stacks 04CO in the étale source** — the Stacks 03LW comparison
  and the identification of defining ideal sheaves, taken in two steps along `ψ` and `φ`, agree
  with the one-step pair along `ψ ≫ φ`.  It is the only ingredient of that clause which is not
  bookkeeping, and it is the one the *pasting* route consumes.  The clause itself needs nothing
  further: it is proved downstream, as
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsConormalAction.lean`, and by the
  route through Stacks 04CP rather than by pasting — so this lemma is not in fact used by it.

## Implementation notes

**The statement below is the closed-subspace case; the immersion case is proved elsewhere.**
Stacks 04CO is stated for an immersion `i : Z ⟶ X`, and
`AlgebraicGeometry.Space.conormalModule` is the conormal module of a closed subspace
`Z : AlgebraicGeometry.Space.ClosedSubspaces B S hS X.1`, so what is proved below is the closed
case, with the inverse image `Z_U` formed as `CategoryTheory.Subfunctor.preimage`, a closed
subspace by Stacks 083Q (`AlgebraicGeometry.Space.isClosedSubspace_preimage`), rather than as a
fibre product.  The tag at the generality it is stated in — an immersion, with `Z_U` locally
closed in `U` — is
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionEtaleRestriction.lean`, for the
conormal module of an immersion taken through the closed factorisation of Stacks 04CE
(`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`), together with
`AlgebraicGeometry.Space.isLocallyClosedSubspace_preimage` there for the locally closed
clause.

**The étale restriction is read through Stacks 03LW.**  The source writes `𝒞_{Z/X}|_{Z_U}` for
the restriction of the conormal module to the small étale site of `Z_U`, which is the étale
restriction functor `AlgebraicGeometry.Space.etaleModulePullback`; the statement below is for
the inverse image of modules `AlgebraicGeometry.Space.modulePullback` along the projection `p`,
and the two are identified by Equation 03LW
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`).  That comparison is used once,
along `φ` itself, which is where étaleness enters: the remaining two steps — the square
comparison and the equality of ideal sheaves — need no étaleness beyond having the étale
restriction functor at all.  The statement below is nevertheless about the inverse image of
modules along `p`, and not about a reindexing of sections: `p` is the base change of `φ` along
the inclusion of `Z`, hence étale, but identifying the inverse image along `p` with the étale
restriction along `p` is one further instance of Stacks 03LW and is not taken here.

**The last step introduces no choice.**  The étale restriction of `𝓘_Z` is *equal* to `𝓘_{Z_U}`,
by `AlgebraicGeometry.Space.etaleModulePullback_definingIdealSheaf_eq`, so the last step could be
taken with `CategoryTheory.eqToIso`.  It is taken instead with
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`, the hand-built isomorphism of the same
two modules, whose components are the identity on the underlying regular functions over every
étale chart by `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_hom_apply_coe`.  That makes
the step canonical on sections rather than a transport along an equality of objects, which is what
the canonicity of the composite rests on.

**Every intermediate functor and object is named, at the top level.**  The three steps are
separate definitions, not `let`-bindings inside the composite.  That is not cosmetic: with the
steps `let`-bound, the forward map of the composite could not be described at all — `rfl` on an
equation for it exhausts the default heartbeat budget in `whnf` — whereas with
the steps named the composite's forward map is their composite by the definition of
`CategoryTheory.Iso.trans`, and each step is characterised separately.

Their types are still written out.  A metavariable left in a `CategoryTheory.Functor.comp`
position in this part of the development drives the unifier through the choice principle hidden
in the pullback of modules and does not terminate, so the types are supplied rather than
inferred.

**Each step is characterised first as an isomorphism and only then on forward maps.**  The `_eq`
lemmas identify a step with the construction it is built from; the `_hom` lemmas then read that
off.  Going directly to the forward map does not work: `AlgebraicGeometry.Space.Modules` and
`CategoryTheory.SheafOfModules` are two spellings of one category here, the defining ideal sheaf
arrives in the second and the inverse image of modules expects the first, so an equation stated
on forward maps is not type-correct at the transparency `CategoryTheory.Functor.mapIso_hom` and
`CategoryTheory.Iso.app_hom` are matched at.  Rewriting at the isomorphism level first and then
applying those two lemmas with `exact` — which needs no motive — avoids that.

## What is not proved

* **The immersion case is not proved.**  Stacks 04CO is stated for an immersion `i : Z ⟶ X`;
  what is proved here is the closed case, because `AlgebraicGeometry.Space.conormalModule` exists
  in this development only for a closed subspace.  The reduction of an immersion to a closed
  immersion (Stacks 04CE, 06EC) is absent; the implementation notes above record this, and it is
  the one clause of the tag that nothing in this development supplies.

* **The functoriality in the étale source `U`.**  **Superseded: it is proved, in a module below
  this one.**  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsConormalAction.lean` states the
  clause with the two-step composite written out and carries the tag there; the route is the one
  the ninth measurement below describes, and the heterogeneous composition law it runs on is
  `AlgebraicGeometry.Space.conormalMap_comp_of_spaces` of that same file.  What this bullet
  records is therefore the cost of this file's terms and the reason the clause is not hosted
  here, not an open obstruction.

  The equation the bullet was originally written about is

  `conormalEtaleRestrictionTwoStep B S hS ψ φ hψ hφ Z =
    (conormalModuleEtaleRestrictionIso B S hS (ψ ≫ φ) hψφ Z).hom`.

  **That equation is not the clause, and it cannot be proved in any module.**  The eleventh
  measurement at the end of this bullet shows that no theorem statement can reproduce the body of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`, so the definition is not the vehicle
  for the clause and has no consumer; the claim above that without its pinning the equation could
  not be stated at all was already corrected by the ninth measurement below.

  **The diagram chase is complete; what is left is bookkeeping.**  With each of the three
  identifications replaced by its three steps the equation becomes a three-by-three square, and
  every ingredient is now available:

  * the two closed subspaces `(ψ ≫ φ)⁻¹(Z)` and `ψ⁻¹(φ⁻¹(Z))` agree and the projections compose,
    by `AlgebraicGeometry.Space.closedSubspacePreimage_comp` and
    `AlgebraicGeometry.Space.subspaceProjection_comp` of
    `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/BaseChange.lean`, both by `rfl`;
  * the square comparisons paste, by `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app`;
  * the fibre over `V` is `AlgebraicGeometry.Space.modulePullbackIdealSheafRestriction_comp`
    above;
  * and those close the square together with exactly **two** naturalities — that of the
    `ψ`-square comparison, and that of Equation 03LW, the second used inside the fibre.

  The chase itself is pure morphism algebra and compiles, with every category, functor, module
  and comparison abstracted to a variable and with the pasting, the fibre lemma above, the
  naturality of the `ψ`-square comparison and `CategoryTheory.Functor.map_comp` as its only
  inputs.  What does not work is *instantiating* it, and that is the whole of what is left.

  **Where the cost is, exactly.**  At the default budget of 200 000, for the two
  spellings `AlgebraicGeometry.Space.conormalModule B S hS X Z` and `(i_Z)^*𝓘_Z` of one object:

  * inside `CategoryTheory.Functor.obj`, with the same functor on both sides — `rfl`, instant;
  * inside `CategoryTheory.NatTrans.app` of `AlgebraicGeometry.Space.modulePullbackCompIso` —
    **does not terminate**.

  So what decides the cost is not that the object is projected out of a construction but *which*
  projection it sits under.  `CategoryTheory.Functor.obj` compares its object argument by
  congruence; `CategoryTheory.NatTrans.app` reduces the projection first, and that drives `whnf`
  into the construction of the inverse image of modules.

  **That obstruction is crossed.**  A heterogeneous equality crosses it at the default budget,
  in 0.2 s:

  `private theorem natTrans_app_heq (t : F ⟶ G) (h : M = N) : HEq (t.app M) (t.app N)`

  by `subst h; rfl`, used as
  `eq_of_heq (natTrans_app_heq _ (AlgebraicGeometry.Space.conormalModule_eq B S hS X Z))`.  It
  works because `eq_of_heq` unifies the two *types* `F.obj M ⟶ G.obj M` and `F.obj N ⟶ G.obj N`
  and never compares the components themselves, so the two spellings meet only inside
  `CategoryTheory.Functor.obj`, which is the free case above.

  **The reconciliations at the isomorphism hold at the default budget**, not merely at a raised
  one — each by `rfl`, together in 1.5 s:

  * `conormalModuleEtaleRestrictionIso B S hS (ψ ≫ φ) hψφ Z` against its three steps written at
    the iterated spelling `ψ⁻¹(φ⁻¹Z)` and with the projection written `q ≫ p`;
  * `conormalModuleEtaleRestrictionIso B S hS ψ hψ (φ⁻¹Z)` against its three steps written at
    that same spelling;
  * the pinned two-step composite, read as an isomorphism, against the same with its `ψ`-step
    expanded.

  `congrArg CategoryTheory.Iso.hom` carries each of these to forward maps, and those three
  rewrites together with the heterogeneous crossing bring the entire goal to one spelling.
  `AlgebraicGeometry.Space.closedSubspacePreimage_comp` and
  `AlgebraicGeometry.Space.subspaceProjection_comp` are then not needed as rewrites at all: the
  reconciliations at the isomorphism absorb them.

  **`unfold` works, and is the right first move.**
  `unfold AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` is instant.  It is what makes the
  above possible, because it exposes the body while leaving
  the goal's own type in place — so the identification of the type pinned to `(ψ ≫ φ)⁻¹Z` with
  the `q ≫ p` spelling that `modulePullbackCompIso q p` carries is never demanded.  Demanding it
  instead, by `show` or by `Eq.trans` against the composite read as an isomorphism, **does not
  terminate**: 800 000, 2 000 000 and 4 000 000 heartbeats were each exhausted.

  **What is left is one identification, and it is not the chase.**  The chase is a lemma of pure
  morphism algebra in a single bare category, with every object a variable and no functor in it
  at all; it compiles, and its conclusion `a ≫ f ≫ r = o` meets the goal with no reduction
  whatever, precisely because every object in it is free.  And all eight ingredients that chase
  consumes can be put in one proof state at the default budget, each elaborating as a `have`:
  the heterogeneous crossing above; the forward map of the identification for `φ`, split by
  `CategoryTheory.Functor.map_comp`; the naturality of the `ψ`-square comparison; the splitting
  of the inverse image along `i_V` of the fibre composite; the forward map of the identification
  for `ψ`, which is `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` at the
  iterated spelling already; `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` at the
  concrete stacked squares, whose three-factor splitting of `CategoryTheory.NatTrans.app` and
  whose three whisker equations are then free; the fibre lemma above, transported along the
  inverse image along `i_V`; and the reconciliation of the one-step identification for `ψ ≫ φ`
  with its three steps.

  **Supplying the implicit arguments explicitly is not the lever.**  Making the chase lemma's
  functors, its natural transformation and its objects explicit and passing every one of them
  does not help: the default budget is exhausted at exactly one argument
  either way.  What fails is a single `isDefEq` *between two of the ingredients* — the inverse
  image along `q` of the inverse image along `i_U` of Equation 03LW at `𝓘_Z`, as
  `CategoryTheory.Functor.map_comp` produces it out of
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` for `φ`, against the same
  morphism as the naturality of `AlgebraicGeometry.Space.conormalPullbackCompIso` for the
  `ψ`-square produces it.  Both are `q^*(i_U^*(-))` of one morphism of modules on `U`.
  Identifying them exhausts the budget, and it does so whichever side is asked to produce the
  other: writing the first out in the second's spelling moves the timeout into that statement.
  Nor does it help to arrange that no composite sits under a `CategoryTheory.Functor.map` at the
  interface — splitting the step into its two factors first leaves the timeout where it was.
  **That identification can be removed rather than performed, but the clause still does not
  close**; what is left is a different `isDefEq`, recorded three paragraphs below.

  **`CategoryTheory.Functor.comp` passes through `obj` for free and through `map` not at all.**
  This is the sharp form of the `CategoryTheory.Functor.obj` versus `CategoryTheory.NatTrans.app`
  dichotomy recorded above, and it is what makes the bookkeeping expensive.  At the concrete
  inverse-image functors and the default budget, `(F ⋙ G).obj M` against `G.obj (F.obj M)` is
  `rfl` and instant, and so is `p^*𝒞_{Z/X}` against `(i_Z ⋙ p)^*𝓘_Z`; but `(F ⋙ G).map f`
  against `G.map (F.map f)` **does not terminate**.  So every step that moves a
  `CategoryTheory.Functor.comp` across a `CategoryTheory.Functor.map` must be made by rewriting
  with `CategoryTheory.Functor.comp_map`, and never by `rfl` or by leaving it to the unifier.

  **Removing that identification works, and is not sufficient.**  The route of stating the
  naturality of the `ψ`-square comparison as a lemma of its own, with its left-hand side the
  right-hand side of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` carried
  along `q`, works.  The form that does it takes the forward map of the
  identification for `φ` as a *variable* `e` and its characterisation as a hypothesis, so that
  the two spellings are never asked to meet:

  ```
  theorem conormalPullbackCompIso_hom_app_naturality (Z) (Z') (g) (f) (hsq)
      {W} {N N' N''} (e : W ⟶ (modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj N'')
      (a : W ⟶ (modulePullback B S hS (subspaceInclusion B S hS X' Z')).obj N)
      (b : N ⟶ N') (c : N' ⟶ N'')
      (he : e = a ≫ (modulePullback B S hS (subspaceInclusion B S hS X' Z')).map b ≫
        (modulePullback B S hS (subspaceInclusion B S hS X' Z')).map c) :
      (modulePullback B S hS f).map e ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app N'' =
        (modulePullback B S hS f).map a ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app N ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
                ((modulePullback B S hS g).map b) ≫
              (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
                ((modulePullback B S hS g).map c)
  ```

  It is proved in 1.0 s, by `CategoryTheory.NatTrans.naturality` rewritten with
  `CategoryTheory.Functor.comp_map` and `CategoryTheory.Functor.map_comp`, and at its instance
  the two sides of the step print character for character the same.  With it the goal no longer
  contains the morphism of the paragraph above at all.  It still does not close, and what is left
  is one `isDefEq` between two spellings of the **projection**.

  **The projection has two spellings, and they are forced from opposite sides.**
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` writes `q : ψ⁻¹(φ⁻¹Z) ⟶ φ⁻¹Z` as
  `ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom)`, which is the spelling of
  `AlgebraicGeometry.Space.subspaceProjection_comp`; but
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` at `ψ` and `φ⁻¹Z`, being an
  instance of a statement about a general closed subspace, can only produce
  `ObjectProperty.homMk ((⟨Z.1.preimage φ.hom, _⟩ : ClosedSubspaces _).1.fromPreimage ψ.hom)`.
  The two differ by one iota reduction, and at the default budget:

  * `q₁ = q₂` by `rfl` — instant;
  * `(modulePullback q₁).obj M = (modulePullback q₂).obj M` by `rfl` — instant;
  * `(modulePullback q₁).map h = (modulePullback q₂).map h` by `rfl` — **does not terminate**.

  So `CategoryTheory.Functor.map` does not pass an iota-crossing of its *functor* argument, where
  `CategoryTheory.Functor.obj` does.  That is the sharp form of the `obj`-versus-`app` dichotomy
  recorded above: it is not special to `CategoryTheory.Functor.comp`, and
  `CategoryTheory.Functor.comp_map` is no help here, since both functors are `modulePullback` of
  iota-equal morphisms.  The same holds under `CategoryTheory.NatTrans.app`: the two instances of
  `AlgebraicGeometry.Space.conormalPullbackCompIso` differing only in that argument do not
  identify either.

  **Neither spelling can be removed.**  Rewriting the goal is out: `rw` with `q₁ = q₂`, and `rw`
  with `AlgebraicGeometry.Space.conormalModule_eq`, each exhaust the budget in `whnf`, although
  both equations are themselves instant.  Writing the body of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` in the second spelling *does*
  typecheck — the file compiles in 25 s — and it does make the naturality step above match on the
  nose; but it breaks the pasting instead.
  `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` composes the two projections as
  `q ≫ p`, and `q₁ ≫ p` against `ObjectProperty.homMk (Z.1.fromPreimage (ψ ≫ φ).hom)` is exactly
  the `rfl` of `AlgebraicGeometry.Space.subspaceProjection_comp`, while `q₂ ≫ p` against it does
  not terminate.  The naturality and the pasting therefore demand opposite spellings of `q`, and
  whichever one the body carries, one of the two steps dies.  That, and not the identification of
  the Stacks 03LW comparison, is the whole of what is left.

  **What is cheap in the same proof state.**  `rw` *does* fire
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` in the unfolded goal, for `φ`,
  for `ψ` at `φ⁻¹Z` and for `ψ ≫ φ`, all three together in 1.45 s — the warning above about `rw`
  is about `CategoryTheory.Functor.map_comp` and `closedSubspacePreimage_comp`, not about this.
  The 3×3 chase, stated in a bare category with every object and morphism a variable, is matched
  against the goal by `apply` in 0.39 s, so instantiating it is not the problem; its ingredients
  each elaborate standalone in about 2 s, including
  `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` at the concrete stacked squares.
  The whiskered right-hand side of that pasting cannot be split by `rw` or by `simp only` with
  `CategoryTheory.NatTrans.comp_app` — neither finds the pattern `(α ≫ β).app X`, which is
  visibly present — but unification splits it when it is passed to the chase, so it needs no
  splitting.  Two further facts hold: `CategoryTheory.NatTrans.app` with the two
  spellings of the conormal module needs the heterogeneous crossing, and raising
  `maxRecDepth` is not a lever — elaborating the naturality instance as a `have` and then
  `exact`ing it reaches `maxRecDepth`, and raising it to 8 000 moves the same failure back to the
  heartbeat limit.

  **The crossings are all payable in an argument, and the mathematical content is proved.**  The
  route of the paragraph before last works, in the form that generalizes nothing: every
  identification of two spellings is handed over in an *argument*, as a heterogeneous equality of
  morphisms or an equation of objects, so that no `CategoryTheory.Functor.map` and no
  `CategoryTheory.NatTrans.app` is ever asked to cross one.  Three lemmas do it, and each
  elaborates and is checked at the default budget:

  * `HEq ((modulePullback f₁).map e) ((modulePullback f₂).map e)` from `A₁ = A₂` and
    `HEq f₁ f₂`, by `subst` — the crossing of the projection, paid in the argument of
    `AlgebraicGeometry.Space.modulePullback`;
  * the same for the upper closed subspace and the projection of
    `AlgebraicGeometry.Space.conormalPullbackCompIso` together, the two square hypotheses being
    identified by `proof_irrel`.  Finishing *that* one with `rfl` instead exhausts the **kernel's**
    budget — `(kernel) deterministic timeout`, a limit distinct from the elaborator's and not
    reported by it;
  * the same for the two morphisms and the module of
    `AlgebraicGeometry.Space.modulePullbackCompIso` at once, which is what carries
    `AlgebraicGeometry.Space.conormalModule_eq` across `CategoryTheory.NatTrans.app`.

  With those in hand the chase closes on the concrete data: the chase lemma in a bare category,
  given the naturality of the `ψ`-square comparison in the `e`-as-a-variable form above, the
  pasting `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` at the two concrete stacked
  squares, and `AlgebraicGeometry.Space.modulePullbackIdealSheafRestriction_comp` transported
  along the inverse image of `i_V` and split by `CategoryTheory.Functor.map_comp`, elaborates and
  passes the kernel, and its conclusion **is** the functoriality equation — written in the
  spelling those three lemmas carry rather than the one the body of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` carries.  So what is left is not
  mathematics and not a missing identification: it is the interface with the goal.

  **Where that interface stands, and the wall.**  `unfold` followed by `rw` of the
  characterisation for `ψ` brings the goal to the five-factor shape the chase consumes, and the
  three structural ingredients and the five crossings can all be given to it.  The assembled
  application sits exactly at the default budget: whether it elaborates or exhausts the budget at
  the fibre argument is decided by caches warmed by the preceding declarations.  And when it does
  elaborate, **the kernel does not accept the term**: `(kernel)
  deterministic timeout`.  No reordering of the arguments addresses that: the kernel re-checks
  every `rfl` the elaborator was handed, and it has none of the elaborator's caches.

  **Two refinements of the above.**  `rw` fires
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` for `ψ` in the unfolded goal but
  *not* for `ψ ≫ φ` afterwards: once the goal holds the other `CategoryTheory.Iso.hom` subterms,
  `rw` tests each of them against the pattern and the budget goes in `whnf`.  The timing
  "all three together in 1.45 s" holds of the bare unfolded goal only, so the characterisation for
  `ψ ≫ φ` has to be supplied as a hypothesis rather than rewritten.  And the two spellings of the
  projection are not themselves the obstruction: both produce the same morphism, and what differs
  — what `CategoryTheory.Functor.map` will not cross — are the *implicit object arguments* of
  `AlgebraicGeometry.Space.modulePullback`, which an instance of a statement about a general
  closed subspace reads off the subspace that statement quantifies over and not off the
  projection it is applied to.

  **The body cannot be written out.**  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`
  against its own body, copied byte for byte out of this file into a theorem statement, is not
  `rfl` at the default budget: `isDefEq` and `whnf` both exhaust it, with `diagnostics
  true` reporting some 3 000 unfoldings of `CategoryTheory.Comma.left`, 2 900 of
  `Opposite.unop`, 1 761 of `CategoryTheory.Functor.obj` and 1 582 of
  `CategoryTheory.NatTrans.app`.  So a hypothesis about a factor of the body cannot be stated by
  hand: the factors have to be read off the goal by passing `_`, and a hole under
  `AlgebraicGeometry.Space.modulePullback` is a first-order pattern and free, while a hole for a
  whole functor argument — `?F.map x` — is higher-order and exhausts the budget.

  **Naming the factors of the body is not the lever — but the chase assembles.**  Suppose the
  two non-trivial factors of the body are made top-level definitions and the `ψ`-side of the
  chase is restated to match them.  Three things then hold; the first two are gains and the third
  is what defeats the route.

  *The `ψ`-side has to be stated over a variable closed subspace of `U`.*  An instance of a
  statement about a general closed subspace carries the spelling
  `(⟨Z.1.preimage φ.hom, _⟩ : ClosedSubspaces _).1.preimage ψ.hom` — the projections of the
  anonymous constructor are not reduced — and the reduced spelling of the right-hand side of
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` at `φ⁻¹(Z)`, written out by
  hand, does **not** cross it: `isDefEq` exhausts the budget.  Stating the ingredients instead as
  lemmas over a variable `Z' : ClosedSubspaces B S hS U.1` and instantiating all of them at
  `Z' = φ⁻¹(Z)` makes every one carry that spelling automatically and costs nothing.  With that
  done **every ingredient of the chase elaborates and the chase closes**: the naturality of the
  `ψ`-square comparison in its split form, the one-step identification characterised with its last
  two factors merged and its square hypothesis taken as a variable — free, by proof irrelevance —
  `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` split into its three factors, the
  fibre lemma transported along `i_V` and split, and the identification for `ψ ≫ φ` carried across
  the two spellings of the upper closed subspace by one heterogeneous equality.

  *Nothing may be done by rewriting.*  `rw` and `simp only` do not fire
  `CategoryTheory.Functor.map_comp`, `CategoryTheory.NatTrans.comp_app` or
  `CategoryTheory.Functor.whiskerLeft_app` on these goals — "did not find an occurrence of the
  pattern", with the pattern printed character for character in the target: an invisible
  instance-argument mismatch on `≫` in `AlgebraicGeometry.Space.Modules`.  Every such step has to
  be a term, `Functor.map_comp F f g` carried by `congrArg` and `Eq.trans`.  And where `rw` does
  fire it is worse than useless: the merged characterisation proved by
  `rw [conormalModuleEtaleRestrictionIso_hom, Functor.map_comp]` is **rejected by the kernel** —
  `(kernel) deterministic timeout` — while the same statement proved by `congrArg` and `Eq.trans`
  is accepted in two seconds, because the kernel re-checks `rw`'s `Eq.mpr` motive without the
  elaborator's caches.  `unfold` has the same problem and is not the escape it looks like: it is
  instant
  for the elaborator, and the declaration whose proof begins with it is rejected by the kernel.

  *A named factor cannot be opened.*  Each of the two named factors against **its own body**, with
  its declared type literally the body's type, is not `rfl` at the default budget:

  * `(modulePullbackCompIso q p).inv.app M` — `whnf` and `isDefEq` both exhaust it;
  * `(modulePullback q).map e` — the same.

  So a factor whose body is a `CategoryTheory.NatTrans.app` or a `CategoryTheory.Functor.map` of
  an inverse image of modules is *opaque*: `whnf` of a `CategoryTheory.Functor.map` at these
  functors unfolds the inverse image down to sheafification and does not terminate, so the name
  cannot be identified with the term it names, by `rfl` or by unification.  Naming such a factor
  therefore buys nothing and costs exactly the step the chase needs.  A factor whose *argument* is
  a morphism is free by contrast, the crossing becoming a congruence under
  `CategoryTheory.Functor.obj` — which is the `obj`-versus-`app` law recorded above, and is where
  a name does pay.

  **Where it stands.**  The chase in a bare category, applied to its
  ingredients as hypotheses with no type ascriptions, **elaborates at the default budget**: the
  functoriality equation exists as a term.  Its type prints character for character identically to
  the statement it is meant to prove, and `exact` on it exhausts the budget at `whnf`.  What
  differs are the implicit object and instance arguments of `≫`, which the two sides solved from
  different places — the statement from what is written there, the term from its ingredients.
  Giving every ingredient an explicit type that pins those arguments moves the timeout into the
  first ingredient; supplying all thirteen of the chase's implicit arguments by name moves it
  there too; `refine` with the conclusion unified first reaches the same wall at the first
  hypothesis.

  **What is cheap, one declaration each in about two seconds**: `(F ⋙ G).obj M` against
  `G.obj (F.obj M)`; the same with
  `conormalModule X Z` written for `i_Z^*𝓘_Z` inside it; `i_{ψ⁻¹Z'}^*𝓘_{ψ⁻¹Z'}` against
  `conormalModule V (ψ⁻¹Z')`; transporting an equation of morphisms across any of those; a
  composition written by hand against the library's `CategoryTheory.Functor.map_comp`; and the
  three-factor splitting of the pasting law, **provided its type is inferred and not declared** —
  as a term with no ascription it costs 2.9 s, and the same equation with its type written out
  does not elaborate.  So the cost of the expanded statement in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionSections.lean` does not come
  from
  mixing the two spellings of one object inside a single composite: the mixing is free, and what
  is not free is declaring the type.

  **The next lever is the instance path, not the factors.**  Every wall above is one `≫` in
  `AlgebraicGeometry.Space.Modules` whose implicit arguments were solved twice over, the two
  solutions never meeting.  A possible remedy is pinning that: stating the pasting law and
  the chase over `CategoryTheory.SheafOfModules` directly, so that the category and its instance
  are the same term in the statement and in the ingredients and no instance unification happens at
  the junction at all.

  **Three further pitfalls.**  `(rfl : A = B)` elaborates to `Eq.refl A`, so
  `congrArg f (rfl : A = B)` has type `f A = f A` and silently loses `B`; a crossing must be
  bound as `have h : A = B := rfl` and used as `congrArg f h`.  After `unfold` the goal is
  type-correct only at default transparency — `AlgebraicGeometry.Space.Modules` and
  `CategoryTheory.SheafOfModules` are the two spellings of one category — so `rw` refuses
  `CategoryTheory.Functor.map_comp` and `closedSubspacePreimage_comp` with "motive is not type
  correct"; those reconciliations have to be made at the isomorphism and transported, never in
  the goal.  And `rw` does not fire `CategoryTheory.Iso.app_hom` or
  `CategoryTheory.Functor.mapIso_hom` on these goals even where the pattern is visibly present,
  while `exact` and `simp` do apply them; expanding the forward map of a
  `CategoryTheory.Iso.trans` chain by definitional unfolding instead costs more than 4 000 000
  heartbeats.  The three reconciliations have to be taken at the isomorphism and not at the
  forward map for the same reason and not only for convenience: the first of them, stated
  directly on forward maps, exhausts the default budget at `whnf`, so
  `congrArg CategoryTheory.Iso.hom` is what carries it and not a `rfl` one spelling down.  And
  the explicit longhand forms of these statements reach `maxRecDepth` before they reach the
  budget — that is a separate limit, and `maxRecDepth 8000` is what they want.

  As noted above, `simp only` must not be used to unfold the two-step composite, since
  it iota-reduces `(⟨_, _⟩ : ClosedSubspaces _).1` and so silently reintroduces the difference of
  spelling it was meant to remove.  So does the one about the body: rewriting the body of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` into the spelling an instantiation
  produces makes the body itself cost a large fraction of the budget and still does not close the
  last identification.

  **The crossing-in-an-argument discipline has an instance in the library, and it is not on
  this clause's route.**  `AlgebraicGeometry.Space.conormalMap_comp_of_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean` is part (3) of
  Stacks 04G2 with the upper edge of the outer rectangle and the comparison of Stacks 03LU handed
  over as variables carrying their values in an equation and a heterogeneous equality — the
  general form of what the three lemmas above do by hand.  It elaborates, the kernel accepts it,
  and it does cross the obstruction it was built for: a composite in the upper-edge argument,
  which is what blocks the restriction stability of condition (3) of Stacks 061A.  It does
  **not** address the residue recorded above.  That residue is not a composite under
  `AlgebraicGeometry.Space.modulePullback` but the two spellings of the *projection's implicit
  object arguments*, and the chase here pastes square comparisons rather than composing conormal
  maps, so part (3) of Stacks 04G2 does not appear in it at all.  The route that would use it
  instead of the pasting is the one the next bullet describes, and that route still needs the
  identification of `AlgebraicGeometry.Space.conormalMap` with the isomorphism constructed here,
  which is not proved; that law alone does not give this clause.

  Proving the clause here adds `ConormalModuleCompositionSections` to this file's import closure,
  for
  the pasting, and `Thickenings/BaseChange`, for the composition law of the projections; the two
  together take the closure to 2359 modules, and there is no cycle.

  **The route through Stacks 04CP reaches the clause, and this file cannot host it.**  With
  `AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean` proved
  unconditionally,
  the route the bullet below describes is available in principle: read both sides through that
  identification and the clause becomes part (3) of Stacks 04G2,
  `AlgebraicGeometry.Space.conormalMap_comp`, at the two stacked étale restriction squares.  It is
  not available *here*.  `ConormalModuleBaseChangeFlat` imports this file, by
  `ConormalModuleBaseChangeFlat → ConormalModuleBaseChangeEpi → ConormalModuleBaseChange →
  ConormalModuleEtaleRestriction`, so the identification is strictly downstream of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`; and `ConormalModuleComposition`, which
  carries the composition law, imports `ConormalModuleCompositionSections`, so that file cannot
  reach the law either.  No module this one may import carries both.  Of the draft tree exactly
  five modules are downstream of both — `Spaces/Groupoids/More/SectionsConormalAction`,
  `Spaces/ConormalSequenceUnramifiedPairSplitting`, `Spaces/Chow/ProperFlatBaseChange`,
  `Spaces/Chow/ProperFlatBaseChangeGenericPoints` and
  `Spaces/Chow/GysinProperPushforwardGenericPoints` — and the clause has to be stated in one of
  them, or in a new module below both.

  **In a module that imports both, every ingredient of that route elaborates, passes the
  kernel and is axiom-clean at the default budget**, the five together in about seven seconds: the
  square of the outer rectangle, by pasting the two étale restriction squares with
  `CategoryTheory.Category.assoc` and two `congrArg`s; the identification at `φ`; the
  identification at `ψ` over the closed subspace `φ⁻¹(Z)` of `U`; the identification at `ψ ≫ φ`
  read at the *iterated* spelling `ψ⁻¹(φ⁻¹Z)` of the upper closed subspace and with the projection
  written as the composite `q ≫ p` — which confirms from the other side that iota-crossings in the
  first-order argument positions of `AlgebraicGeometry.Space.conormalMap` are free, so that neither
  `AlgebraicGeometry.Space.closedSubspacePreimage_comp` nor
  `AlgebraicGeometry.Space.subspaceProjection_comp` has to be rewritten; and
  `AlgebraicGeometry.Space.conormalMap_comp` itself at the two stacked squares.  A congruence lemma
  in a bare category, with the inverse-image functor, the objects and the first factor all *read
  off its hypotheses* rather than written down, replaces the two inner conormal maps by the two
  isomorphisms of Stacks 04CO, and the assembled term's type prints character for character as the
  body of `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`.

  **What is left is one `isDefEq`.**  It is neither
  the two spellings of the projection nor the Stacks 03LW comparison.
  `AlgebraicGeometry.Space.conormalMap_comp` *quantifies* over its three closed subspaces, so its
  conclusion can only spell the ambient algebraic space of each as `⟨Z.1.toFunctor, Z.2.1⟩` of the
  subspace it was instantiated at — a `Subtype.val` of an anonymous constructor, unreduced —
  whereas the signature of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` and the body
  of `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` spell them reduced.  The two differ
  by that one iota reduction, and it sits in the implicit object arguments of
  `AlgebraicGeometry.Space.modulePullback`, of `AlgebraicGeometry.Space.modulePullbackCompIso` and
  of `CategoryTheory.Functor.map`.  On that one goal, at the default budget:

  * `delta AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` is instant and leaves the two
    sides printing identically.  Unlike `unfold` it changes the goal's type instead of rewriting
    through an `Eq.mpr`, so it is not the kernel problem recorded above — it is the right way to
    open
    the composite, and it still does not close the goal;
  * `with_reducible rfl` on the opened goal **fails**: the iota sits under
    `CategoryTheory.Functor.map`, which does not cross it;
  * `rfl` exhausts the budget at `whnf`, and `congrArg` on the last factor at `isDefEq`;
  * with the closed subspaces written `AlgebraicGeometry.Space.preimageSubspace` throughout, so
    that the gap is an abbreviation's delta as well as the iota, `with_reducible rfl` *does* cross
    it in seconds — and the declaration is then **rejected by the kernel**, `(kernel) deterministic
    timeout`.  So the gap is reducible-only and the kernel still will not pay it;
  * writing the composite out by hand does not escape this.  Both the natural spelling and one
    pinned by type ascriptions to the law's own spelling elaborate as *statements* — so even
    without the pinning of `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` the equation
    can be stated; what it cannot do is match what a lemma produces.  With `maxRecDepth
    8000` raised, the congruence step then moves with the spelling and exhausts the budget itself.

  So what the clause waits on is neither mathematics nor a diagram chase: it is a host below both
  modules, and a variant of `AlgebraicGeometry.Space.conormalMap_comp` whose conclusion's
  inverse-image functors are indexed by terms the consumer supplies — the discipline of
  `AlgebraicGeometry.Space.conormalMap_comp_of_eq`, which hands over the upper edge and the
  Stacks 03LU comparison in arguments, applied instead to the *ambient algebraic spaces of the two
  upper closed subspaces*.  With that the five ingredients above close the clause with no `rfl` in
  it at all.

  **The body of a `def` in this development is not the body a theorem can write, and the cause
  is Lean's abstraction of nested proofs.**  This rules out, generically rather than locally,
  stating the body of `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` as an equation
  and proving it by `rfl`.

  * *The body equation already exists.*  Lean generates
    `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep.eq_def` on demand, and its
    right-hand side is the stored body; any module importing this one may use it by name, so a
    hand-written copy would be a duplicate as well as unprovable.
  * *A hand-written copy is not provable.*  Copied byte for byte out of this file into a theorem
    statement, at the default budget of 200 000: the statement itself elaborates, and `rfl`
    exhausts the budget at `whnf` and at `isDefEq`;
    `delta AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` is instant and leaves the two
    sides printing character for character the same, after which `rfl` exhausts the budget at
    `isDefEq`, `with_reducible rfl` fails with a `whnf` timeout, and `congr 1` exhausts it at
    `whnf`.  Writing the body on the left instead, so that it is elaborated with no expected type,
    changes nothing — the term it elaborates to is the same one.
  * *Why.*  Compared argument by argument rather than by printing — the printer elides these terms
    long before they end, so a character diff proves nothing — the two sides are two different
    terms, and not by a little.  The stored body has 638 585 nodes, the hand-written one
    5 675 879; all seven arguments of the top-level `CategoryTheory.CategoryStruct.comp` differ,
    the two morphism factors by 220 173 against 1 611 375 and by 306 979 against 2 990 237.  The
    stored body uses fifteen auxiliary proof constants —
    `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep._proof_1` through `._proof_7`,
    together with the inherited ones of
    `AlgebraicGeometry.Space.conormalEtaleRestrictionSquareApp` and of
    `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` — and the hand-written one uses
    none: Lean abstracts the nested proofs of a *definition*'s body into auxiliary constants and
    does not do that to a *theorem*'s statement.  Those proofs sit inside the
    `(⟨_, _⟩ : AlgebraicSpaces B S hS)` that indexes `AlgebraicGeometry.Space.modulePullback`,
    hence in type positions and not in positions proof irrelevance reaches, so identifying the two
    sides means unfolding all fifteen of them under a `CategoryTheory.Functor.map` and a
    `CategoryTheory.NatTrans.app`.  That is the `obj`-versus-`app` law recorded above, now with a
    cause, and it is why naming a factor of such a body buys nothing.
  * *So the definition is a dead end, and not only here.*  In a module that imports
    `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsConormalAction.lean`, the
    literal
    equation with `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` on the left does not
    close either: `exact` of the proved clause exhausts the budget at `whnf`, `delta` followed by
    `exact` at `isDefEq`, and `(conormalEtaleRestrictionTwoStep.eq_def …).trans` of the proved
    clause at `whnf`.  The proved clause writes the composite out for precisely this reason.
    `AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep` accordingly has no consumer in the
    library — outside this file's prose its only occurrence is its own definition.

* **That the canonical map of Stacks 04CP is this isomorphism.**  It is proved with no
  hypothesis, by `AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean`, downstream of this
  file; the `restrict` field of `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` that
  the route below needs is constructed by
  `Space.modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit`.
  For the square below, `AlgebraicGeometry.Space.conormalMap` gives a morphism
  `p^*𝒞_{Z/X} ⟶ 𝒞_{Z_U/U}`, and Stacks 04CO read together with Stacks 04CP says that it is the
  isomorphism constructed here.  Identifying the two amounts to identifying
  `AlgebraicGeometry.Space.idealSheafMap` — which is defined by transposing twice — with the
  Stacks 03LW comparison followed by the equality of ideal sheaves.  That identification is the
  content of Stacks 04G2 and 04CQ rather than of 04CO.

  **The two descriptions meet at the structure sheaf.**  The characterisation
  `AlgebraicGeometry.Space.idealSheafMap_transpose` describes `idealSheafMap` only after both
  transposes, while `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`
  describes the comparison only after the unit of the extension of scalars.  At the **structure
  sheaf** they are brought to a common form by
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStructureSheaf.lean`: Equation
  03LW at `𝒪_X`, read as a module over itself, *is*
  `AlgebraicGeometry.Space.structureModulePullbackMap`, the two-fold transpose of pullback of
  regular functions.  The common form is the corepresentability comparison
  `AlgebraicGeometry.Space.modulePullbackUnitIso` of Stacks 03LU, which the chartwise
  description reaches by semilinearity out of the unit module and the Equation 03LW description
  by comparing the transposes along Stacks 03CZ on underlying sheaves of sets.  What remains for
  this bullet is the passage from the structure sheaf to the defining ideal sheaf inside it.

  This identification gives a second route to the functoriality clause above, since the canonical
  map of Stacks 04CP has a composition law for a pasted square —
  `AlgebraicGeometry.Space.conormalMap_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`, part (3) of
  Stacks 04G2 — which would supply the functoriality without the pasting of square comparisons.
  As recorded in the bullet above, the identification is proved and the route does reach the clause,
  and it reaches it in a
  module that imports both this file's identification and the composition law — which, the
  identification being downstream of this file, no module this file may import can be.

  **The two maps are comparable, and the interface between them is crossed.**  The
  equation `conormalMap … = (conormalModuleEtaleRestrictionIso …).hom` *elaborates* at the default
  budget with no transport of any kind: the canonical map of Stacks 04CP at the square of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` and the forward map constructed here
  have, on the nose, the same source and the same target.  So the identification is well posed as
  an equation of morphisms, and no `HEq` and no `CategoryTheory.eqToHom` is needed to state it.
  `AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean` proves it from one
  hypothesis, elaborates and passes the kernel in 30 s, and is axiom-clean.

  **What is left is exactly one equation, and it is a statement about Stacks 03LW alone.**  The
  two maps share their comparison factor on the nose — `conormalPullbackComparison` at the
  étale restriction square against the forward map of
  `AlgebraicGeometry.Space.conormalEtaleRestrictionSquareApp` — so after
  `AlgebraicGeometry.Space.conormalMap_eq` and
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom` the whole difference is the
  second factor, and `CategoryTheory.Functor.map_comp` reduces it to the fibre over the *lower*
  space `U`:

  `idealSheafMap … = (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app 𝓘_Z ≫`
  `  (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom`.

  That equation mentions no closed subspace of `U` in any category, so none of the iota crossings
  recorded in the bullet above occurs in it.  Both sides are morphisms out of `φ^*𝓘_Z`, hence
  determined by their chartwise transposes
  (`AlgebraicGeometry.Space.injective_modulePullbackHomFMap`), that is, by their values on the
  unit sections of `AlgebraicGeometry.Space.modulePullbackUnitSection`; on the left that value is
  `AlgebraicGeometry.Space.chartDiagramPullback` by
  `AlgebraicGeometry.Space.idealSheafMap_unitSection_coe`, and the last factor on the right is the
  identity on underlying regular functions by
  `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_hom_apply_coe`.  So the equation is
  equivalent to: **the comparison of Stacks 03LW carries the unit section of `s` over a chart
  diagram to `s`.**  That is the `restrict` field of
  `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackComparison.lean`, which
  `Space.modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit` constructs.
  This is the sharp form of what the two descriptions above need in order to meet — the
  unit sections are taken along the adjunction of Stacks 03D7 and
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` and
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit` are
  stated past the unit of the extension of scalars, the bridge between the two being the chain of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitChain.lean`.

  **The crossing that the interface needs.**  Writing the canonical map at the
  `AlgebraicGeometry.Space.preimageSubspace` spelling and the comparison at the spelling used in
  this file puts two iota-different spellings of the *lower* category in one statement, and the
  cost depends entirely on where the crossing is asked for:

  * `conormalPullbackComparison … = (conormalEtaleRestrictionSquareApp …).hom` — the statement
    elaborates, and `rfl` on it **exhausts the budget at `isDefEq`**; so does
    `(conormalEtaleRestrictionSquareApp_hom …).symm`.  This is the `obj`-versus-`app` law again:
    the crossing sits under `CategoryTheory.NatTrans.app`.
  * the same crossing taken one level up, as an equation of the two spellings of
    `AlgebraicGeometry.Space.conormalPullbackCompIso` itself — `with_reducible rfl`, **instant**,
    and `congrArg (fun α ↦ α.hom.app 𝓘_Z)` carries it to forward maps for nothing.
  * `CategoryTheory.Functor.map` of iota-different *functor* arguments still does not cross:
    assembling the chain with `AlgebraicGeometry.Space.conormalMap_eq` instantiated at the
    `preimageSubspace` spelling while the remaining factors carry this file's spelling exhausts
    the budget, because the two `AlgebraicGeometry.Space.modulePullback`s differ inside a
    `CategoryTheory.Functor.map`.  Instantiating `conormalMap_eq` at *this file's* spelling
    instead moves every crossing into argument positions of the constants
    `AlgebraicGeometry.Space.conormalMap` and `AlgebraicGeometry.Space.idealSheafMap`, where it is
    first-order and free.  That is the whole trick, and it is cheaper than the heterogeneous
    equalities the bullet above needs.

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V X : AlgebraicSpaces B S hS}

/-! ### The square of the inverse image of a closed subspace -/

/-- **The inverse image of a closed subspace sits in a commutative square.**  For a morphism
`φ : U ⟶ X` of algebraic spaces and a closed subspace `Z ⊆ X`, the inclusion of `Z_U = φ⁻¹(Z)`
followed by `φ` is the projection `p : Z_U ⟶ Z` followed by the inclusion of `Z`.

This is `CategoryTheory.Subfunctor.fromPreimage_ι` read in the category of algebraic spaces; it
is the square that the functoriality of the conormal module of
[Stacks Project, Tag 04CP] consumes. -/
theorem conormalEtaleRestrictionSquare (φ : U ⟶ X) (Z : ClosedSubspaces B S hS X.1) :
    subspaceInclusion B S hS U (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1) ≫ φ =
      (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
          (⟨(Z.1.preimage φ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        subspaceInclusion B S hS X Z :=
  ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Z.1 φ.hom).symm

/-! ### The three steps of the identification -/

/-- **Step one: the square comparison.**  The square `i_U ≫ φ = p ≫ i` of
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` identifies `p^*i^*` with `i_U^*φ^*`;
evaluated at the defining ideal sheaf of `Z` this is an isomorphism `p^*i^*𝓘_Z ≅ i_U^*φ^*𝓘_Z`.

The source is spelled `p^*i^*𝓘_Z` rather than `p^*𝒞_{Z/X}`, which is the same object: that is the
type the square comparison has on the nose, so the equations below need no transport. -/
noncomputable def conormalEtaleRestrictionSquareApp (φ : U ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
            (⟨(Z.1.preimage φ.hom).toFunctor,
                (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≅
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        ((modulePullback B S hS φ).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  (conormalPullbackCompIso B S hS
      (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1) Z φ
      (ObjectProperty.homMk (Z.1.fromPreimage φ.hom))
      (conormalEtaleRestrictionSquare B S hS φ Z)).app
    (definingIdealSheaf B S hS X Z).toSheafOfModules

/-- Step one of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` *is* the square
comparison `AlgebraicGeometry.Space.conormalPullbackCompIso` at the defining ideal sheaf. -/
theorem conormalEtaleRestrictionSquareApp_eq (φ : U ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    conormalEtaleRestrictionSquareApp B S hS φ Z =
      (conormalPullbackCompIso B S hS
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1) Z φ
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom))
          (conormalEtaleRestrictionSquare B S hS φ Z)).app
        (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  rfl

/-- The forward map of step one of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`. -/
theorem conormalEtaleRestrictionSquareApp_hom (φ : U ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    (conormalEtaleRestrictionSquareApp B S hS φ Z).hom =
      (conormalPullbackCompIso B S hS
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1) Z φ
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom))
          (conormalEtaleRestrictionSquare B S hS φ Z)).hom.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules := by
  rw [conormalEtaleRestrictionSquareApp_eq]
  exact Iso.app_hom _ _

/-- **Step two: the inverse image along `φ` is étale restriction.**  The inverse image along the
inclusion of `Z_U` of the identification of [Stacks Project, Tag 03LW], at the defining ideal
sheaf of `Z`: an isomorphism `i_U^*φ^*𝓘_Z ≅ i_U^*(𝓘_Z|_U)`. -/
noncomputable def conormalEtaleRestrictionPullbackComparison (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        ((modulePullback B S hS φ).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≅
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        ((etaleModulePullback.{u, u} B S hS φ hφ).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  (modulePullback B S hS (subspaceInclusion B S hS U
      (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1))).mapIso
    ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
      (definingIdealSheaf B S hS X Z).toSheafOfModules)

/-- Step two of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` *is* the inverse
image along the inclusion of `Z_U` of the Stacks 03LW comparison at the defining ideal sheaf. -/
theorem conormalEtaleRestrictionPullbackComparison_eq (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1) :
    conormalEtaleRestrictionPullbackComparison B S hS φ hφ Z =
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).mapIso
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  rfl

/-- The forward map of step two of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`. -/
theorem conormalEtaleRestrictionPullbackComparison_hom (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1) :
    (conormalEtaleRestrictionPullbackComparison B S hS φ hφ Z).hom =
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).map
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) := by
  rw [conormalEtaleRestrictionPullbackComparison_eq]
  exact (Functor.mapIso_hom _ _).trans (congrArg _ (Iso.app_hom _ _))

/-- **Step three: the ideal sheaf of the inverse image.**  The inverse image along the inclusion
of `Z_U` of the identification `𝓘_Z|_U ≅ 𝓘_{Z_U}` of
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`: an isomorphism
`i_U^*(𝓘_Z|_U) ≅ 𝒞_{Z_U/U}`. -/
noncomputable def conormalEtaleRestrictionIdealIso (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        ((etaleModulePullback.{u, u} B S hS φ hφ).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≅
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1)).toSheafOfModules :=
  (modulePullback B S hS (subspaceInclusion B S hS U
      (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1))).mapIso
    (etaleIdealSheafRestrictionIso B S hS φ hφ Z)

/-- Step three of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` *is* the inverse
image along the inclusion of `Z_U` of
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`. -/
theorem conormalEtaleRestrictionIdealIso_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    conormalEtaleRestrictionIdealIso B S hS φ hφ Z =
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).mapIso
        (etaleIdealSheafRestrictionIso B S hS φ hφ Z) :=
  rfl

/-- The forward map of step three of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`. -/
theorem conormalEtaleRestrictionIdealIso_hom (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (conormalEtaleRestrictionIdealIso B S hS φ hφ Z).hom =
      (modulePullback B S hS (subspaceInclusion B S hS U
          (⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).map
        (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom := by
  rw [conormalEtaleRestrictionIdealIso_eq]
  exact Functor.mapIso_hom _ _

/-! ### The conormal module of the inverse image -/

/-- **Stacks 04CO for the conormal module.**  Let `φ : U ⟶ X` be an étale morphism of algebraic
spaces and `Z ⊆ X` a closed subspace, with inverse image `Z_U = U ×_X Z` and projection
`p : Z_U ⟶ Z`.  Then the inverse image along `p` of the conormal module of `Z` in `X` is the
conormal module of `Z_U` in `U`:

`𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.

The isomorphism is the square comparison `p^*i^* ≅ i_U^*φ^*` of
`AlgebraicGeometry.Space.conormalPullbackCompIso`, then the inverse image along `i_U` of the
identification of `φ^*` with étale restriction of [Stacks Project, Tag 03LW], then the equality
`𝓘_Z|_U = 𝓘_{Z_U}` of defining ideal sheaves. -/
@[stacks 04CO "the conormal module commutes with etale base change",
  sga "3 I 6.8.5" "étale base change"]
noncomputable def conormalModuleEtaleRestrictionIso (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
            (⟨(Z.1.preimage φ.hom).toFunctor,
                (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS X Z) ≅
      conormalModule B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1) :=
  conormalEtaleRestrictionSquareApp B S hS φ Z ≪≫
    conormalEtaleRestrictionPullbackComparison B S hS φ hφ Z ≪≫
      conormalEtaleRestrictionIdealIso B S hS φ hφ Z

/-- **The isomorphism of Stacks 04CO is the composite of its three steps.**  This is the
structural equation of `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`: the three
factors are named, so the equation holds by the definition of `CategoryTheory.Iso.trans` and no
unfolding of the steps is required. -/
theorem conormalModuleEtaleRestrictionIso_hom_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (conormalModuleEtaleRestrictionIso B S hS φ hφ Z).hom =
      (conormalEtaleRestrictionSquareApp B S hS φ Z).hom ≫
        (conormalEtaleRestrictionPullbackComparison B S hS φ hφ Z).hom ≫
          (conormalEtaleRestrictionIdealIso B S hS φ hφ Z).hom :=
  rfl

/-- **The characterising equation of Stacks 04CO for the conormal module.**  The forward map of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` is the square comparison of
`AlgebraicGeometry.Space.conormalPullbackCompIso` at the defining ideal sheaf, followed by the
inverse image along the inclusion of `Z_U` of first the Stacks 03LW comparison and then
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`.

This is the equation a consumer needs: the isomorphism is otherwise only a term, and nothing can
be proved about it without a description of its forward map in terms that pre-exist it. -/
theorem conormalModuleEtaleRestrictionIso_hom (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (conormalModuleEtaleRestrictionIso B S hS φ hφ Z).hom =
      (conormalPullbackCompIso B S hS
            (⟨Z.1.preimage φ.hom,
              isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
              ClosedSubspaces B S hS U.1) Z φ
            (ObjectProperty.homMk (Z.1.fromPreimage φ.hom))
            (conormalEtaleRestrictionSquare B S hS φ Z)).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS U
            (⟨Z.1.preimage φ.hom,
              isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
              ClosedSubspaces B S hS U.1))).map
            ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePullback B S hS (subspaceInclusion B S hS U
              (⟨Z.1.preimage φ.hom,
                isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
                ClosedSubspaces B S hS U.1))).map
              (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom := by
  rw [conormalModuleEtaleRestrictionIso_hom_eq, conormalEtaleRestrictionSquareApp_hom,
    conormalEtaleRestrictionPullbackComparison_hom, conormalEtaleRestrictionIdealIso_hom]

/-- The two-step restriction of the isomorphism of Stacks 04CO along a further étale
`ψ : V ⟶ U`: the comparison of the inverse images along the two projections, then the inverse
image along `q` of the identification for `φ`, then the identification for `ψ`.

The type is written in the spelling the one-step identification for `ψ ≫ φ` carries — the
projection `r` and the closed subspace `(ψ ≫ φ)⁻¹(Z)` — rather than the iterated spelling the
body produces; the two agree by `AlgebraicGeometry.Space.subspaceProjection_comp` and
`AlgebraicGeometry.Space.closedSubspacePreimage_comp`, and pinning the type here is what lets
the functoriality equation below be stated at all. -/
noncomputable def conormalEtaleRestrictionTwoStep (ψ : V ⟶ U) (φ : U ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS (ObjectProperty.homMk (Z.1.fromPreimage (ψ ≫ φ).hom) :
          (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
              (isClosedSubspace_preimage B S hS (ψ ≫ φ).hom Z.1 X.2 V.2 Z.2).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj (conormalModule B S hS X Z) ⟶
      conormalModule B S hS V (⟨Z.1.preimage (ψ ≫ φ).hom,
          isClosedSubspace_preimage B S hS (ψ ≫ φ).hom Z.1 X.2 V.2 Z.2⟩ :
          ClosedSubspaces B S hS V.1) :=
  (modulePullbackCompIso B S hS (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
          (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
                (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨(Z.1.preimage φ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
            AlgebraicSpaces B S hS)) (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
          (⟨(Z.1.preimage φ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).inv.app (conormalModule B S hS X Z) ≫
    (modulePullback B S hS (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
          (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
                (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨(Z.1.preimage φ.hom).toFunctor,
              (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
            AlgebraicSpaces B S hS))).map
        (conormalModuleEtaleRestrictionIso B S hS φ hφ Z).hom ≫
      (conormalModuleEtaleRestrictionIso B S hS ψ hψ (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1)).hom

/-! ### The fibre of the identification over the lower space -/

/-- Pure morphism algebra: the two composition laws — of the Stacks 03LU comparison of inverse
images against Stacks 03LW, and of the identifications of defining ideal sheaves — together with
one naturality compose to the fibre of the identification of Stacks 04CO over the lower space.

The statement is at the level of a bare category so that none of its steps can drive the unifier
into the construction of the inverse image of modules; see the implementation notes of this
file. -/
private theorem comp_eq_of_unit_laws {C : Type*} [Category C] {A A' A'' D E F G H : C}
    (a : A ⟶ A') (a' : A' ⟶ A) (u : A' ⟶ A'') (y : A'' ⟶ D) (z : D ⟶ E) (pp : A' ⟶ F)
    (w : F ⟶ D) (w₁ : F ⟶ G) (w₂ : G ⟶ D) (c : G ⟶ H) (er : H ⟶ E) (b : A ⟶ H)
    (hnat : u ≫ y = pp ≫ w) (hw : w = w₁ ≫ w₂) (hE : w₂ ≫ z = c ≫ er)
    (hΛ : a' ≫ b = pp ≫ w₁ ≫ c) (haa : a ≫ a' = 𝟙 A) :
    a ≫ u ≫ y ≫ z = b ≫ er := by
  rw [reassoc_of% hnat, hw, Category.assoc, hE, ← reassoc_of% hΛ, reassoc_of% haa]

/-- **The fibre over the lower space of the functoriality of Stacks 04CO in the étale source.**
For étale `ψ : V ⟶ U` and `φ : U ⟶ X` with étale composite, the comparison of inverse images
along a composite of [Stacks Project, Tag 03LU], followed by the inverse image along `ψ` of the
Stacks 03LW comparison for `φ` and of the identification `𝓘_Z|_U = 𝓘_{Z_U}`, followed by the same
two for `ψ`, is the Stacks 03LW comparison and the identification for `ψ ≫ φ` taken in one step.

This is the one ingredient of the functoriality in the étale source that is not bookkeeping: it
is the compatibility of the comparison of inverse images with étale restriction,
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, whose hypothesis on
the two units of étale restriction along a composite is discharged by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`, together with the composition
law `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_comp` of the identifications of
defining ideal sheaves and the naturality of Equation 03LW.  The two sides are read at the two
spellings `ψ⁻¹(φ⁻¹Z)` and `(ψ ≫ φ)⁻¹Z` of the inverse image, which agree; the statement is
formed because the reconciliation sits in an argument of `definingIdealSheaf` rather than inside
a `CategoryTheory.Functor.map`.

What the functoriality clause of Stacks 04CO still needs on top of this is recorded under "What
is not proved" below. -/
theorem modulePullbackIdealSheafRestriction_comp (ψ : V ⟶ U) (φ : U ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) (hφ : IsEtale B S hS φ.hom)
    (hψφ : IsEtale B S hS (ψ ≫ φ).hom) (Z : ClosedSubspaces B S hS X.1) :
    (modulePullbackCompIso B S hS ψ φ).inv.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (modulePullback B S hS ψ).map
            ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
                (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
              (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom) ≫
          (modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom.app
              (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
                isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
                ClosedSubspaces B S hS U.1)).toSheafOfModules ≫
            (etaleIdealSheafRestrictionIso B S hS ψ hψ (⟨Z.1.preimage φ.hom,
              isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
              ClosedSubspaces B S hS U.1)).hom =
      (modulePullbackIsoEtaleModulePullback B S hS (ψ ≫ φ) hψφ).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (etaleIdealSheafRestrictionIso B S hS (ψ ≫ φ) hψφ Z).hom :=
  comp_eq_of_unit_laws _ _ _ _ _ _ _ _ _ _ _ _
    ((modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom.naturality _)
    (Functor.map_comp (etaleModulePullback.{u, u} B S hS ψ hψ) _ _)
    (etaleIdealSheafRestrictionIso_comp B S hS ψ φ hψ hφ hψφ Z)
    (NatTrans.congr_app
      (modulePullbackCompIso_hom_comp_etaleRestriction B S hS ψ φ hψ hφ hψφ
        (etaleModulePullbackCompAdjunction_unit B S hS ψ φ hψ hφ hψφ))
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (Iso.inv_hom_id_app (modulePullbackCompIso B S hS ψ φ)
      (definingIdealSheaf B S hS X Z).toSheafOfModules)

end AlgebraicGeometry.Space

end
