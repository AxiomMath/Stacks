module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounitFromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsIso
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesUnique
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineSiteAssociatedModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceTransitivity
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# Stacks 03LC (3) at `τ = étale`: the gap discharged

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of a big étale site and let `𝓕`
be a quasi-coherent `𝒪_X`-module.  `StacksDraft.AlgebraicGeometry.Descent.AssociatedModule`
`.SmallEtalePushforwardSquare` reduced part (3) of [Stacks, Tag 03LC] at `τ = étale` to a single
statement:  that `f_{small, *}(𝓕^a)` is quasi-coherent on `Y_étale`.  This file proves it, and
with it the two remaining conjuncts of that part.

The route is the source's.  For `U ⟶ V` a morphism of **affine** objects of the small étale site
of `Y`, the base-change map of `f_{small, *}(𝓕^a)` is

`Γ(V ×_Y X, p_V^*𝓕) ⊗_{Γ(V, 𝒪)} Γ(U, 𝒪) ⟶ Γ(U ×_Y X, p_U^*𝓕)`,

which is [Stacks, Tag 02KH] (1) in degree `0` over an affine base.  That it is an isomorphism is
condition (1) of [Stacks, Tag 0GZX] for that module, so the restriction of
`f_{small, *}(𝓕^a)` to the affine objects is quasi-coherent there by 0GZX (1) ⇒ (2);
`AlgebraicGeometry.SmallEtale.isIso_counit_of_affineRestriction` then makes the counit of the
associated-module adjunction of `Y_étale` an isomorphism at `f_{small, *}(𝓕^a)`, which both
proves the quasi-coherence conjunct and gives the commuting square of part (3).

## What is new here, and what is not

The mathematics of the base change is **already in the library**, twice over:
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` on sheaves
over an arbitrary base, and
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` on sections
over an affine one.  What was missing, and is supplied here, is the **bridge**: that the
site-theoretic base-change map `Stacks.SheafOfModules.canonicalMap` of the pushforward *is* that
comparison.  The two could not be composed before, because neither mentions the other's map, and
because the group of sections they are stated about carries two different scalar structures.

## Main definitions

* `AlgebraicGeometry.SmallEtale.bcOver`, `bcProj`, `bcStruct`, `bcMap`: the base change `W ×_Y X`
  of an object of the small étale site of `Y`, as a scheme over `X`, with its projection to `W`,
  its structure morphism to `X`, and its functoriality.
* `AlgebraicGeometry.SmallEtale.pushforwardSectionsAlgebra` and `pushforwardSectionsModule`: the
  scalar structures the base-change map of the small étale ringed site carries, named at the
  spelling `Γ(-, ⊤)` so that they can be passed to the statements below rather than searched
  for.
* `AlgebraicGeometry.SmallEtale.bcSectionsComparison`: the comparison `ρ^*(p_V^*𝓕) ≅ p_U^*𝓕` of
  `Stacks.Sites.pullbackSectionsComparison`, read on global sections.
* `AlgebraicGeometry.SmallEtale.smallPushforwardAssociatedModuleValIso`: the comparison of
  Stacks, Remark 03FH, on the two direct images, read on underlying presheaves of modules.
* `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs`: **the square of
  Stacks 03LC part (3) at `τ = étale`**, with no hypothesis beyond those of the part.

## Main results

* `AlgebraicGeometry.SmallEtale.isPullback_bcMap`: **the geometric input.**  The square whose
  top is `U ×_Y X ⟶ V ×_Y X`, whose bottom is `U ⟶ V` and whose vertical morphisms are the
  base-change projections is cartesian.
* `AlgebraicGeometry.SmallEtale.isModule_pushforward_eq_baseModule`: **the awkward step.**  The
  two scalar structures on the group `Γ(W ×_Y X, p_W^*𝓕)` — the one the direct image on the site
  carries, and the one
  `Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule` builds — agree.
* `AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_pushforward_sections` and
  `SmallEtale.smallAffineEtale_isIso_canonicalMap_smallPushforward_associatedModule`:
  **the bridge.**  The base-change map of `f_{small, *}(𝓕^a)` between affine objects is an
  isomorphism.
* `AlgebraicGeometry.SmallEtale.restrictionBaseChange_smallPushforward_tmul`,
  `AlgebraicGeometry.SmallEtale.smul_sections_smallPushforward` and
  `AlgebraicGeometry.SmallEtale.associatedPresheaf_map_smallEtaleBaseChange`: the three named
  steps the bridge is read off in;  see the implementation notes.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward_associatedModule`: the
  second conjunct of Stacks 03LC part (3) at `τ = étale`, read at an associated module.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward`: **the second conjunct
  of Stacks 03LC part (3) at `τ = étale`**, at every quasi-coherent `𝒪`-module on `X_étale`.

## Implementation notes

**The two scalar structures.**  The sections of `f_{small, *}(𝓕^a)` over `W` are the sections of
`𝓕^a` over `W ×_Y X`, and the scalars of `Γ(W, 𝒪)` act on them through
`AlgebraicGeometry.Scheme.Hom.appTop` of the base-change projection `W ×_Y X ⟶ W`, that being
the structure map of the morphism of ringed sites.
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` instead
makes them act through `appLE ⊤ ⊤`.  The two ring maps are *equal* —
`AlgebraicGeometry.SmallEtale.appTop_eq_appLE` — but not definitionally so, `appLE` carrying an
application of `CategoryTheory.Functor.map` to an identity;  and since the scalar structure
occurs in the *type* of the tensor product the base-change map is defined on, the two statements
cannot be composed until they are identified.  This is the same obstruction as
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseModule_eq_instModule`, at the sections of
a direct image on a site rather than on a space.

Rather than transport the conclusion of the base-change theorem along that equation of
instances — which leaves the instances in the transported statement unreachable by synthesis, so
that `map_add` and `Equiv.bijective` no longer elaborate at the tensor product —
`AlgebraicGeometry.SmallEtale.exists_linearEquiv_sections_baseChange_of_eq` restates it with the
algebra and the module structure as *named* parameters pinned by equations, in the shape of
`Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections`.  A caller
then passes the structures its own goal carries and owes only the two equations.

**The induction over the tensor product** is carried out at abstract rings and modules, in
`AlgebraicGeometry.SmallEtale.bijective_of_tmul_eq`, and not at the concrete section types:  the
`AddCommMonoid` instance of the tensor product is not found by synthesis there, and the defeq
checks at those types are expensive enough that the elaboration does not terminate within any
reasonable elaboration budget.

**Where the sections of the direct image meet the sections of a pullback.**  The sections of
`f_{small, *}(𝓕^a)` over `W` *are* `Γ(W ×_Y X, p_W^*𝓕)`, but only after the fibre product
`W ×_Y X` has been unfolded, and that unfolding is what makes the identification expensive: the
fibre product is a chosen limit, so its cone cannot reduce and the elaborator retries.  Three
disciplines keep it affordable, and every statement in this file obeys them.

*Identify at the morphism level, apply the element afterwards.*  The restriction maps of `𝓕^a`
are the pullback maps on sections of Stacks 03DS;  that identification is stated as an equation of
morphisms of abelian groups, in
`AlgebraicGeometry.SmallEtale.associatedPresheaf_map_smallEtaleBaseChange`, and applied to a
section only in
`AlgebraicGeometry.SmallEtale.restrictionBaseChange_pushforward_tmul_gamma`, where the abelian
group the section lives in is the one the statement already names.  Applied to an element, the
identification would instead have to reconcile the two groups, and with them the two function-like
instances of their morphisms.

*Write the base change into the statement rather than leaving it to a parameter.*  A statement
proved at an abstract object of the small étale site of `X` is cheap, but *instantiating* it at
`W ×_Y X` is not:  the instance was chosen for a variable and has to be matched against the one
instance synthesis finds at the fibre product.  So
`AlgebraicGeometry.SmallEtale.associatedPresheaf_map_smallEtaleBaseChange`,
`AlgebraicGeometry.SmallEtale.smul_sections_smallPushforward` and
`AlgebraicGeometry.SmallEtale.exists_equiv_sections_baseChange_bcMap` all mention
`AlgebraicGeometry.smallEtaleBaseChange` explicitly, and the parameters they do take -- the sheaf
of modules, the object and the arrow of the small étale site of `Y` -- are instantiated at the
very terms their consumers' statements contain.

*Leave nothing to be solved for.*  `AlgebraicGeometry.SmallEtale.bijective_of_tmul_eq` is applied
through `AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_of_tmul_eq`, which writes the
source of the base-change comparison as the extension of scalars it is, so that the two rings, the
module and the two scalar structures are read off the presheaf and the arrow;  and the additivity
and the bijectivity of the comparison are taken from the `map_add` and `LinearEquiv.bijective`
lemmas rather than from the fields of the linear equivalence, which cannot be projected out
without unfolding `Stacks.Sites.pullbackSectionsComparison` at the fibre product.  By the same
token `AlgebraicGeometry.SmallEtale.isIso_canonicalMap_smallAffineEtaleModuleRestriction` takes its
hypothesis by name instead of as an instance:  the two maps are the same term, but instance
synthesis sees that only after the base-change map of a ringed site is unfolded into the adjoint
transpose it abbreviates.

**The spelling of the base change** is `((SmallEtale.toOver B X.obj X.property).obj
((smallEtaleBaseChange B a).obj W)).left` throughout, rather than
`(SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B a).obj W)`.  The two are
definitionally equal, but `AlgebraicGeometry.pullbackSectionsMap` — the restriction map of the
associated presheaf of Stacks 03DU, which is what the restriction map of `𝓕^a` *is* under
`AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections` — produces the first, and the
module structure on the sections of a module on a scheme is found by synthesis only at the
spelling the scheme is written in.

**The quasi-compactness and quasi-separatedness of `W ×_Y X`** come from the cartesian square:
the base-change projection is the base change of `f`, so it is quasi-compact and quasi-separated,
and over an affine `W` that is quasi-compactness and quasi-separatedness of the space, by
`AlgebraicGeometry.quasiCompact_iff_compactSpace` and
`AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace`.

**The attributes.**  Two declarations carry `@[stacks 03LC]`, with clause strings naming the
conjunct and the topology: the quasi-coherence conjunct of part (3) at `τ = étale`, at every
quasi-coherent `𝒪`-module on `X_étale`, and the commuting square of that part.  The reading of
the conjunct at an associated module is an intermediate step and is left untagged, being
subsumed by the general one.  The bridge itself carries **no** attribute: it is a special case
of Tag 02KH (1) in degree `0` and of Tag 0GZX (1), neither of which it settles, and the audit
scanner matches the bare tag.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.PresheafOfModules
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-! ### The base change of an object of the small étale site of `Y` -/

/-- The base change `W ×_Y X` of an object of the small étale site of `Y`, as a scheme over
`X`. -/
public abbrev bcOver (W : SmallEtale B Y.obj Y.property) : Over X.obj :=
  (SmallEtale.toOver B X.obj X.property).obj ((smallEtaleBaseChange B a).obj W)

/-- The base-change projection `W ×_Y X ⟶ W`. -/
public abbrev bcProj (W : SmallEtale B Y.obj Y.property) :
    (bcOver B a W).left ⟶ (SmallEtale.toScheme B Y.obj Y.property).obj W :=
  (smallEtaleProjection B a).app W

/-- The structure morphism `W ×_Y X ⟶ X` of the base change. -/
public abbrev bcStruct (W : SmallEtale B Y.obj Y.property) : (bcOver B a W).left ⟶ X.obj :=
  (bcOver B a W).hom

/-- The base change of a morphism of the small étale site of `Y`. -/
public abbrev bcMap {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    (bcOver B a U).left ⟶ (bcOver B a V).left :=
  ((SmallEtale.toOver B X.obj X.property).map ((smallEtaleBaseChange B a).map g)).left

/-- The base change of an object of the small étale site of `Y` is a fibre product. -/
public theorem isPullback_bcProj (W : SmallEtale B Y.obj Y.property) :
    IsPullback (bcProj B a W) (bcStruct B a W)
      (B.inclusion.map (Over.hom W.obj)) (schemeHom B a) :=
  isPullback_smallEtaleBaseChange B a W

/-- **The base change of a morphism of the small étale site of `Y` is a fibre-product square.**
The square whose top is `U ×_Y X ⟶ V ×_Y X`, whose bottom is `U ⟶ V` and whose vertical
morphisms are the base-change projections is cartesian:  the outer square and the lower square
of the vertical pasting with the structure morphisms to `X` and to `Y` are both cartesian by
`AlgebraicGeometry.SmallEtale.isPullback_bcProj`. -/
public theorem isPullback_bcMap {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    IsPullback (bcMap B a g) (bcProj B a U) (bcProj B a V)
      ((SmallEtale.toScheme B Y.obj Y.property).map g) := by
  refine (IsPullback.of_bot (h₃₁ := schemeHom B a) ?_ ?_ (isPullback_bcProj B a V)).flip
  · rw [Over.w ((SmallEtale.toOver B X.obj X.property).map ((smallEtaleBaseChange B a).map g)),
      toScheme_map_comp_structure B g]
    exact isPullback_bcProj B a U
  · exact ((smallEtaleProjection B a).naturality g).symm

/-! ### The two scalar structures on one group of sections -/

variable (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent]

/-- Over the whole space, pullback of global functions along a morphism of schemes is
`AlgebraicGeometry.Scheme.Hom.appLE` at `⊤`. -/
public theorem appTop_eq_appLE {Z W : Scheme.{u}} (h : Z ⟶ W) :
    h.appTop = h.appLE ⊤ ⊤ (le_preimage_top h ⊤) :=
  (appLE_top_eq_app h).symm

/-- **The base algebra structure of a morphism of schemes is extension of scalars along the
restriction map of global functions.**  The two ring maps agree only propositionally, `appLE`
at `⊤` carrying an application of `CategoryTheory.Functor.map` to an identity. -/
public theorem baseAlgebra_eq {Z W : Scheme.{u}} (h : Z ⟶ W) :
    h.appTop.hom.toAlgebra = baseAlgebra h :=
  congrArg (fun t : Γ(W, ⊤) ⟶ Γ(Z, ⊤) => RingHom.toAlgebra t.hom) (appTop_eq_appLE h)

/-- **The one genuinely awkward step: the two scalar structures on the sections of
`f_{small, *}(𝓕^a)` over `W` agree.**  The site-theoretic structure restricts scalars along the
pullback of global functions along the base-change projection `W ×_Y X ⟶ W`, and
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule` restricts them along
`AlgebraicGeometry.Scheme.Hom.appLE` of that morphism at `⊤`.  The two are **not**
definitionally equal — `appLE ⊤ ⊤` is only propositionally `app ⊤` — and the instance occurs in
the *type* of the tensor product the base-change map is defined on, so the two statements cannot
be composed until they are identified. -/
public theorem isModule_pushforward_eq_baseModule (W : SmallEtale B Y.obj Y.property) :
    (((smallPushforward B a).obj (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj
        (op W)).isModule
      = baseModule (bcProj B a W) ((Scheme.Modules.pullback (bcStruct B a W)).obj 𝓕) ⊤ :=
  Module.ext (by
    funext r x
    exact congrArg (fun t : Γ((SmallEtale.toScheme B Y.obj Y.property).obj W, ⊤) ⟶
          Γ((bcOver B a W).left, ⊤) =>
        (CommRingCat.Hom.hom t) r •
          (show ↑Γ((Scheme.Modules.pullback (bcStruct B a W)).obj 𝓕, ⊤) from x))
      (appTop_eq_appLE (bcProj B a W)))

/-- The `Γ(V, 𝒪)`-algebra structure on `Γ(U, 𝒪)` that the base-change map of the small étale
ringed site extends scalars along, at the spelling `Γ(-, ⊤)`. -/
@[instance_reducible]
public def pushforwardSectionsAlgebra {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    Algebra Γ((SmallEtale.toScheme B Y.obj Y.property).obj V, ⊤)
      Γ((SmallEtale.toScheme B Y.obj Y.property).obj U, ⊤) :=
  ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom.toAlgebra

/-- The `Γ(W, 𝒪)`-module structure on the sections of `f_{small, *}(𝓕^a)` over `W`, at the
spelling `Γ(-, ⊤)`. -/
@[instance_reducible]
public def pushforwardSectionsModule (W : SmallEtale B Y.obj Y.property) :
    Module Γ((SmallEtale.toScheme B Y.obj Y.property).obj W, ⊤)
      Γ((Scheme.Modules.pullback (bcStruct B a W)).obj 𝓕, ⊤) :=
  (((smallPushforward B a).obj
    (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op W)).isModule

/-! ### Two abstract reductions -/

/-- **Bijectivity of a map out of a base change, from its values on pure tensors.**  Stated for
abstract rings and modules so that the induction over the tensor product is not carried out at
the concrete section types, where the two scalar structures are not found by instance synthesis;
they are therefore named, so that a caller can pass the ones its goal carries. -/
public theorem bijective_of_tmul_eq {R S : Type u} [CommRing R] [CommRing S]
    [alg : Algebra R S] {M : Type u} [AddCommGroup M] [mod : Module R M]
    {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
    (ψ : TensorProduct R S M → N') (hψ : ∀ u v, ψ (u + v) = ψ u + ψ v)
    (e : TensorProduct R S M ≃ N) (he : ∀ u v, e (u + v) = e u + e v)
    (β : N → N') (hβ : ∀ u v, β (u + v) = β u + β v) (hβbij : Function.Bijective β)
    (h : ∀ (b : S) (x : M), ψ (b ⊗ₜ[R] x) = β (e (b ⊗ₜ[R] x))) :
    Function.Bijective ψ := by
  have key : ∀ z, ψ z = β (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        exact (AddMonoidHom.mk' ψ hψ).map_zero.trans
          (AddMonoidHom.mk' (fun w => β (e w))
            (fun u v => (congrArg β (he u v)).trans (hβ _ _))).map_zero.symm
    | tmul b x => exact h b x
    | add u v hu hv => rw [hψ, he, hβ, hu, hv]
  refine ⟨fun u v huv => ?_, fun z => ?_⟩
  · exact e.injective (hβbij.1 ((key u).symm.trans (huv.trans (key v))))
  · obtain ⟨n, hn⟩ := hβbij.2 z
    exact ⟨e.symm n, (key _).trans (by rw [e.apply_symm_apply, hn])⟩

/-- **Cartesianness of a restriction map from the values of its base-change comparison on pure
tensors.**  `AlgebraicGeometry.SmallEtale.bijective_of_tmul_eq` with the source of the comparison
written as the extension of scalars that it is, rather than as an abstract tensor product:  the
two rings, the module and the two scalar structures are then read off the presheaf of modules and
the arrow, so that a caller instantiating this statement solves for nothing.  That is the whole
point of the restatement -- recovering them by unifying an abstract tensor product against the
type of a supplied map is what forces the sections of the direct image to be reconciled with the
sections of a pullback, and that reconciliation is expensive at a fibre product. -/
public theorem isIso_restrictionBaseChange_of_tmul_eq
    {C : Type (u + 1)} [Category.{u} C] {Rc : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (Rc ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    {U V : Cᵒᵖ} (h : U ⟶ V) {N : Type u} [AddCommGroup N]
    (e : ↑((ModuleCat.extendScalars (Rc.map h).hom).obj (M.obj U)) ≃ N)
    (he : ∀ p q, e (p + q) = e p + e q)
    (β : N → ↑(M.obj V)) (hβ : ∀ p q, β (p + q) = β p + β q)
    (hβbij : Function.Bijective β)
    (key : ∀ (r : ↑(Rc.obj V)) (m : ↑(M.obj U)),
      restrictionBaseChange (R := Rc) M h (r ⊗ₜ[↑(Rc.obj U),(Rc.map h).hom] m) =
        β (e (r ⊗ₜ[↑(Rc.obj U),(Rc.map h).hom] m))) :
    IsIso (restrictionBaseChange (R := Rc) M h) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_of_tmul_eq (R := ↑(Rc.obj U)) (S := ↑(Rc.obj V)) (M := ↑(M.obj U))
    (alg := RingHom.toAlgebra (Rc.map h).hom) (mod := (M.obj U).isModule)
    _ (fun p q => map_add (ConcreteCategory.hom (restrictionBaseChange (R := Rc) M h)) p q)
    e he β hβ hβbij key

/-- **Degree-zero flat base change on sections, with the two scalar structures named.**
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` stated for
any `Γ(S, ⊤)`-algebra structure on `Γ(T, ⊤)` and any `Γ(S, ⊤)`-module structure on `Γ(F, ⊤)`
*equal* to the ones that statement builds.  A caller whose goal already carries such structures
— for instance the sections of a direct image on a site, whose scalars are restricted along
`AlgebraicGeometry.Scheme.Γ` rather than along `appLE ⊤ ⊤` — can then pass its own, instead of
transporting the conclusion along an equation of instances. -/
public theorem exists_linearEquiv_sections_baseChange_of_eq
    {S T Z W : Scheme.{u}} {q : T ⟶ S} {iX : Z ⟶ S} {p : W ⟶ Z} {k : W ⟶ T}
    (H : IsPullback p k iX q)
    [AlgebraicGeometry.IsAffine S] [AlgebraicGeometry.IsAffine T] [Flat q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (F : Z.Modules) [F.IsQuasicoherent]
    [alg : Algebra Γ(S, ⊤) Γ(T, ⊤)] (halg : alg = baseAlgebra q)
    [mod : Module Γ(S, ⊤) Γ(F, ⊤)] (hmod : mod = baseModule iX F ⊤) :
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
    ∃ e : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, ⊤) ≃ₗ[Γ(T, ⊤)]
        Γ((Scheme.Modules.pullback p).obj F, ⊤),
      ∀ (b : Γ(T, ⊤)) (x : Γ(F, ⊤)),
        e (b ⊗ₜ[Γ(S, ⊤)] x) = b • pullbackSectionsHom p F ⊤ ⊤ (le_preimage_top p ⊤) x := by
  subst halg
  subst hmod
  exact exists_linearEquiv_sections_baseChange H F

/-! ### The two sides of the comparison on a pure tensor -/

/-- The comparison `ρ^*(q_V^*𝓕) ≅ q_U^*𝓕` of `Stacks.Sites.pullbackSectionsComparison`, read on
global sections. -/
public abbrev bcSectionsComparison {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :=
  AlgebraicGeometry.sectionsLinearEquivOfIso (Stacks.Sites.pullbackSectionsComparison 𝓕
    ((SmallEtale.toOver B X.obj X.property).map ((smallEtaleBaseChange B a).map g))) ⊤

/-- **The base-change map of the direct image on a pure tensor, at any sheaf of modules on
`X_étale`.**  `Stacks.PresheafOfModules.restrictionBaseChange_tmul` at the sections of
`f_{small, *}𝒢`:  the scalar acts through the structure map of `ε_a`, and the restriction map of
the direct image is the restriction map of `𝒢` along the base change of the arrow.

The sheaf of modules is a *parameter*, and both the scalar and the section of the right-hand side
are given the spellings they have over the small étale site of `X`, so that nothing about the
associated module is reconciled here. -/
public theorem restrictionBaseChange_smallPushforward_tmul
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (b : ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op U)))
    (m : ↑(((smallPushforward B a).obj N).val.obj (op V))) :
    restrictionBaseChange (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
        ((smallPushforward B a).obj N).val g.op
        (b ⊗ₜ[↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op V)),
          ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom] m) =
      (show ↑((structureSheaf B X.obj X.property).obj.obj
          (op ((smallEtaleBaseChange B a).obj U))) from
        ((smallEtaleStructureMapRing B a).hom.app (op U)).hom b) •
        (show ↑(N.val.obj (op ((smallEtaleBaseChange B a).obj U))) from
          N.val.map ((smallEtaleBaseChange B a).map g).op m) :=
  restrictionBaseChange_tmul _ _ b m

/-- **The two scalar actions on the sections of `f_{small, *}(𝓕^a)` over `W` agree, read on an
element.**  The site-theoretic action, restricting scalars along the structure map of `ε_a`, and
the action of `Γ(W ×_Y X, 𝒪)` on `Γ(W ×_Y X, p_W^*𝓕)` found by instance synthesis at the
spelling `Γ(-, ⊤)`, are the same.

Both the scalar and the section are variables, so that this identification of the two readings is
the *only* thing that happens:  the identification of the sections of `f_{small, *}(𝓕^a)` over
`W` with `Γ(W ×_Y X, p_W^*𝓕)` costs nothing beyond matching the two carriers. -/
public theorem smul_sections_smallPushforward (W : SmallEtale B Y.obj Y.property)
    (b : ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op W)))
    (m : ↑((associatedModuleOfSections B X.obj X.property 𝓕).val.obj
      (op ((smallEtaleBaseChange B a).obj W)))) :
    (show ↑((structureSheaf B X.obj X.property).obj.obj
        (op ((smallEtaleBaseChange B a).obj W))) from
      ((smallEtaleStructureMapRing B a).hom.app (op W)).hom b) • m =
      ((bcProj B a W).appTop).hom b •
        (show ↑Γ((Scheme.Modules.pullback (bcStruct B a W)).obj 𝓕, ⊤) from m) :=
  rfl

/-- **The restriction map of the presheaf of Stacks 03DS along the base change of an arrow** is
the pullback map on sections of that base change.

`Stacks.Sites.associatedPresheaf_map_eq` with the arrow written out as
`(smallEtaleBaseChange B a).map g`.  The statement is an equation of morphisms of abelian groups
and is deliberately not applied to a section:  with no element present the two sides are the same
term, whereas identifying the two abelian groups of sections over a fibre product -- the group the
presheaf of modules underlying `𝓕^a` carries, and the group of sections of a pullback -- is where
the fibre product has to be unfolded.  A consumer applies the equation to a section afterwards,
with `congrArg`. -/
public theorem associatedPresheaf_map_smallEtaleBaseChange
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    (Stacks.Sites.associatedPresheaf X.obj 𝓕 (SmallEtale.toOver B X.obj X.property)).map
        ((smallEtaleBaseChange B a).map g).op =
      AlgebraicGeometry.pullbackSectionsMap 𝓕
        ((SmallEtale.toOver B X.obj X.property).map
          ((smallEtaleBaseChange B a).map g)) :=
  Stacks.Sites.associatedPresheaf_map_eq X.obj 𝓕
    (SmallEtale.toOver B X.obj X.property) ((smallEtaleBaseChange B a).map g).op

/-- **The restriction map of the presheaf of Stacks 03DS, read on a section**, is the pullback
map on sections: `Stacks.Sites.associatedPresheaf_map_eq` applied to a section. -/
public theorem associatedPresheaf_map_apply_eq_pullbackSectionsMap
    {W₁ W₂ : (SmallEtale B X.obj X.property)ᵒᵖ} (k : W₁ ⟶ W₂)
    (x : ↑((Stacks.Sites.associatedPresheaf X.obj 𝓕
      (SmallEtale.toOver B X.obj X.property)).obj W₁)) :
    (Stacks.Sites.associatedPresheaf X.obj 𝓕
          (SmallEtale.toOver B X.obj X.property)).map k x =
      AlgebraicGeometry.pullbackSectionsMap 𝓕
        ((SmallEtale.toOver B X.obj X.property).map k.unop) x :=
  congrArg (fun t => t x) (Stacks.Sites.associatedPresheaf_map_eq X.obj 𝓕
    (SmallEtale.toOver B X.obj X.property) k)

/-- **The restriction map of `𝓕^a` is the restriction map of the presheaf of Stacks 03DS, read
on a section.**  The presheaf of abelian groups underlying `𝓕^a` *is* that presheaf
(`AlgebraicGeometry.SmallEtale.associatedModuleOfSections_presheaf`), so this holds by `rfl`.

Deciding that `rfl` is what the elaborator spends its budget on here, and the statement is
written to spend as little of it as possible.  With `#count_heartbeats`: 188,160 as
below; 241,110 with the arrow written `h.op` for an `h` of the site rather than an arbitrary
arrow of its opposite; and 479,022 with the arrow written out as `(smallEtaleBaseChange B a).map
g`, which makes the base-change functor's action on morphisms unfold on both sides of the
identification.  The arrow is therefore left a *variable* of the opposite category, and the
consumers instantiate it, which is substitution and costs nothing. -/
public theorem val_map_apply_eq_associatedPresheaf_map_apply
    {W₁ W₂ : (SmallEtale B X.obj X.property)ᵒᵖ} (k : W₁ ⟶ W₂)
    (x : ↑((associatedModuleOfSections B X.obj X.property 𝓕).val.obj W₁)) :
    (associatedModuleOfSections B X.obj X.property 𝓕).val.map k x =
      (Stacks.Sites.associatedPresheaf X.obj 𝓕
        (SmallEtale.toOver B X.obj X.property)).map k x :=
  rfl

/-- **The restriction map of `𝓕^a`, read on a section, is the pullback map on sections.**  The
two preceding lemmas composed, still at an arbitrary arrow of the opposite site. -/
public theorem val_map_apply_eq_pullbackSectionsMap
    {W₁ W₂ : (SmallEtale B X.obj X.property)ᵒᵖ} (k : W₁ ⟶ W₂)
    (x : ↑((associatedModuleOfSections B X.obj X.property 𝓕).val.obj W₁)) :
    (associatedModuleOfSections B X.obj X.property 𝓕).val.map k x =
      AlgebraicGeometry.pullbackSectionsMap 𝓕
        ((SmallEtale.toOver B X.obj X.property).map k.unop) x :=
  (val_map_apply_eq_associatedPresheaf_map_apply (B := B) (𝓕 := 𝓕) k x).trans
    (associatedPresheaf_map_apply_eq_pullbackSectionsMap (B := B) (𝓕 := 𝓕) k x)

/-- **The base-change map of the pushforward on a pure tensor**, with the scalar read as the
pullback of global functions along the base-change projection.  This is
`Stacks.PresheafOfModules.restrictionBaseChange_tmul` at the sections of the pushforward, whose
restriction map is the restriction map of the associated presheaf of Stacks 03DU.

Read off in named steps:  the comparison on a pure tensor at an arbitrary sheaf of modules is
`AlgebraicGeometry.SmallEtale.restrictionBaseChange_smallPushforward_tmul`;  the scalar is the
pullback of global functions along the base-change projection, and the sections of the direct
image are the sections of a pullback, by
`AlgebraicGeometry.SmallEtale.smul_sections_smallPushforward`;  and the restriction map of `𝓕^a`
is the pullback map on sections by
`AlgebraicGeometry.SmallEtale.val_map_apply_eq_pullbackSectionsMap`, which is instantiated at the
arrow only here, where the abelian group it lands in is the one the statement already names. -/
public theorem restrictionBaseChange_pushforward_tmul_gamma
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (b : ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op U)))
    (x : ↑(((smallPushforward B a).obj
      (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V))) :
    restrictionBaseChange (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
        ((smallPushforward B a).obj
          (associatedModuleOfSections B X.obj X.property 𝓕)).val g.op
        (b ⊗ₜ[↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op V)),
          ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom] x) =
      ((bcProj B a U).appTop).hom b •
        AlgebraicGeometry.pullbackSectionsMap 𝓕
          ((SmallEtale.toOver B X.obj X.property).map
            ((smallEtaleBaseChange B a).map g)) x := by
  refine (restrictionBaseChange_smallPushforward_tmul B a
    (associatedModuleOfSections B X.obj X.property 𝓕) g b x).trans ?_
  refine (smul_sections_smallPushforward B a 𝓕 U b
    ((associatedModuleOfSections B X.obj X.property 𝓕).val.map
      ((smallEtaleBaseChange B a).map g).op x)).trans ?_
  refine congrArg
    (fun m : ↑Γ((Scheme.Modules.pullback (bcStruct B a U)).obj 𝓕, ⊤) =>
      ((bcProj B a U).appTop).hom b • m) ?_
  have h := val_map_apply_eq_pullbackSectionsMap (B := B) (𝓕 := 𝓕)
    ((smallEtaleBaseChange B a).map g).op x
  -- `exact h` asks for the goal and `h` to be identified in one step, carriers of the two
  -- equations included, and runs out of heartbeats; the two sides one at a time are cheap.
  refine Eq.trans ?l (Eq.trans h ?r)
  case l => rfl
  case r => rfl

/-- **The base-change map of the pushforward on a pure tensor**, with the scalar read as
`AlgebraicGeometry.Scheme.Hom.appLE` at `⊤`, which is the spelling
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule` uses. -/
public theorem restrictionBaseChange_pushforward_tmul
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (b : ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op U)))
    (x : ↑(((smallPushforward B a).obj
      (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V))) :
    restrictionBaseChange (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
        ((smallPushforward B a).obj
          (associatedModuleOfSections B X.obj X.property 𝓕)).val g.op
        (b ⊗ₜ[↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op V)),
          ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom] x) =
      ((bcProj B a U).appLE ⊤ ⊤ (le_preimage_top (bcProj B a U) ⊤)).hom b •
        AlgebraicGeometry.pullbackSectionsMap 𝓕
          ((SmallEtale.toOver B X.obj X.property).map
            ((smallEtaleBaseChange B a).map g)) x :=
  (restrictionBaseChange_pushforward_tmul_gamma B a 𝓕 g b x).trans
    (congrArg (fun t : Γ((SmallEtale.toScheme B Y.obj Y.property).obj U, ⊤) ⟶
          Γ((bcOver B a U).left, ⊤) =>
        (CommRingCat.Hom.hom t) b •
          AlgebraicGeometry.pullbackSectionsMap 𝓕
            ((SmallEtale.toOver B X.obj X.property).map
              ((smallEtaleBaseChange B a).map g)) x)
      (appTop_eq_appLE (bcProj B a U)))

/-- **The comparison on a scalar multiple of the pullback of a section, with the base change
abstract.**  For a morphism `φ : P ⟶ Q` of schemes over `S` and any morphism `pr : P.left ⟶ W`,
`Stacks.Sites.pullbackSectionsComparison` carries a `Γ(W, 𝒪)`-multiple of the pullback of a
section to the corresponding multiple of `AlgebraicGeometry.pullbackSectionsMap`.

The two schemes over `S` are *parameters* rather than the base change `W ×_Y X` the caller
instantiates them at, and that is what makes the proof cheap: matching the scalar action of
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule` against the one the linear equivalence
carries then unfolds `Module.compHom` and stops.  At the base change itself it instead unfolds
`AlgebraicGeometry.smallEtaleBaseChange` through `CategoryTheory.Over.post` into the fibre-product
cone — the elaborator's reduction counters there are dominated by `Limits.limit.cone` at 92252
unfoldings, `smallEtaleBaseChange` at 66346 and `Over.post` at 52228 — and does not finish inside
any reasonable heartbeat budget. -/
public theorem sectionsComparison_smul_pullbackSectionsHom {S W : Scheme.{u}} (F : S.Modules)
    {P Q : Over S} (φ : P ⟶ Q) (pr : P.left ⟶ W) (b : Γ(W, ⊤))
    (x : Γ((Scheme.Modules.pullback Q.hom).obj F, ⊤)) :
    letI := baseModule pr ((Scheme.Modules.pullback φ.left).obj
      ((Scheme.Modules.pullback Q.hom).obj F)) ⊤
    AlgebraicGeometry.sectionsLinearEquivOfIso
        (Stacks.Sites.pullbackSectionsComparison F φ) ⊤
        (b • pullbackSectionsHom φ.left ((Scheme.Modules.pullback Q.hom).obj F) ⊤ ⊤
          (le_preimage_top φ.left ⊤) x) =
      (pr.appLE ⊤ ⊤ (le_preimage_top pr ⊤)).hom b •
        AlgebraicGeometry.pullbackSectionsMap F φ x :=
  (map_smul (AlgebraicGeometry.sectionsLinearEquivOfIso
      (Stacks.Sites.pullbackSectionsComparison F φ) ⊤)
      ((pr.appLE ⊤ ⊤ (le_preimage_top pr ⊤)).hom b) _).trans
    (congrArg (fun w => (pr.appLE ⊤ ⊤ (le_preimage_top pr ⊤)).hom b • w)
      (Stacks.Sites.pullbackSectionsComparison_pullbackSection F φ
        (le_preimage_top φ.left ⊤) x))

omit [SheafOfModules.IsQuasicoherent 𝓕] in
/-- **The comparison on the pullback of a section.**  This is
`AlgebraicGeometry.SmallEtale.sectionsComparison_smul_pullbackSectionsHom` at the base change
`W ×_Y X`. -/
public theorem bcSectionsComparison_smul_pullbackSectionsHom
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (b : Γ((SmallEtale.toScheme B Y.obj Y.property).obj U, ⊤))
    (x : Γ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕, ⊤)) :
    letI := baseModule (bcProj B a U) ((Scheme.Modules.pullback (bcMap B a g)).obj
      ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕)) ⊤
    bcSectionsComparison B a 𝓕 g
        (b • pullbackSectionsHom (bcMap B a g)
          ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕) ⊤ ⊤
          (le_preimage_top (bcMap B a g) ⊤) x) =
      ((bcProj B a U).appLE ⊤ ⊤ (le_preimage_top (bcProj B a U) ⊤)).hom b •
        AlgebraicGeometry.pullbackSectionsMap 𝓕
          ((SmallEtale.toOver B X.obj X.property).map
            ((smallEtaleBaseChange B a).map g)) x :=
  sectionsComparison_smul_pullbackSectionsHom 𝓕
    ((SmallEtale.toOver B X.obj X.property).map ((smallEtaleBaseChange B a).map g))
    (bcProj B a U) b x

/-! ### The side conditions -/

/-- The base change of an affine object of the small étale site of `Y` along a quasi-compact
morphism is quasi-compact. -/
public theorem compactSpace_bcOver [QuasiCompact (schemeHom B a)]
    (V : SmallEtale B Y.obj Y.property)
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] :
    CompactSpace (bcOver B a V).left :=
  (quasiCompact_iff_compactSpace (bcProj B a V)).mp
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_bcProj B a V).flip
      inferInstance)

/-- The base change of an affine object of the small étale site of `Y` along a quasi-separated
morphism is quasi-separated. -/
public theorem quasiSeparatedSpace_bcOver [QuasiSeparated (schemeHom B a)]
    (V : SmallEtale B Y.obj Y.property)
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] :
    QuasiSeparatedSpace (bcOver B a V).left :=
  (quasiSeparated_iff_quasiSeparatedSpace (bcProj B a V)).mp
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_bcProj B a V).flip
      inferInstance)

/-- The pullback of `𝓕` to the base change of an object is quasi-coherent. -/
public instance isQuasicoherent_pullback_bcStruct (V : SmallEtale B Y.obj Y.property) :
    ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback (bcStruct B a V) 𝓕 inferInstance

/-! ### Cartesianness -/

/-- **Degree-zero flat base change at the base change of an arrow of the small étale site of
`Y`, read at the source of the base-change map of the site.**
`AlgebraicGeometry.SmallEtale.exists_linearEquiv_sections_baseChange_of_eq` applied to the
cartesian square `AlgebraicGeometry.SmallEtale.isPullback_bcMap`, with the two scalar structures
of `AlgebraicGeometry.SmallEtale.pushforwardSectionsAlgebra` and
`AlgebraicGeometry.SmallEtale.pushforwardSectionsModule` passed to it.

Everything the conclusion mentions is spelled as
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_of_tmul_eq` and
`AlgebraicGeometry.SmallEtale.restrictionBaseChange_pushforward_tmul` spell it:  the source of
the equivalence is the extension of scalars the base-change map of the site is defined on, and the
scalar and the section of the formula on a pure tensor are the arguments of that map.  So all the
work of matching the sections of `f_{small, *}(𝓕^a)` over an object against the global sections of
a pullback is done here, once, and the consumer below substitutes. -/
public theorem exists_equiv_sections_baseChange_bcMap
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj U)]
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] :
    letI := baseModule (bcProj B a U) ((Scheme.Modules.pullback (bcMap B a g)).obj
      ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕)) ⊤
    letI : Module ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op V))
        ↑(((smallPushforward B a).obj
          (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V)) :=
      (((smallPushforward B a).obj
        (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V)).isModule
    ∃ ε : ↑((ModuleCat.extendScalars
          ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom).obj
        (((smallPushforward B a).obj
          (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V))) ≃
        Γ((Scheme.Modules.pullback (bcMap B a g)).obj
          ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕), ⊤),
      (∀ p q, ε (p + q) = ε p + ε q) ∧
      ∀ (b : ↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op U)))
        (x : ↑(((smallPushforward B a).obj
          (associatedModuleOfSections B X.obj X.property 𝓕)).val.obj (op V))),
        ε (b ⊗ₜ[↑((smallEtaleRingedSite B Y.obj Y.property).O.obj.obj (op V)),
            ((smallEtaleRingedSite B Y.obj Y.property).O.obj.map g.op).hom] x) =
          (show Γ((SmallEtale.toScheme B Y.obj Y.property).obj U, ⊤) from b) •
            pullbackSectionsHom (bcMap B a g)
              ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕) ⊤ ⊤
              (le_preimage_top (bcMap B a g) ⊤)
              (show Γ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕, ⊤) from x) := by
  have _ := compactSpace_bcOver B a V
  have _ := quasiSeparatedSpace_bcOver B a V
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange_of_eq (isPullback_bcMap B a g)
    ((Scheme.Modules.pullback (bcStruct B a V)).obj 𝓕)
    (alg := pushforwardSectionsAlgebra B g)
    (baseAlgebra_eq ((SmallEtale.toScheme B Y.obj Y.property).map g))
    (mod := pushforwardSectionsModule B a 𝓕 V)
    (isModule_pushforward_eq_baseModule B a 𝓕 V)
  exact ⟨e.toEquiv, e.map_add', he⟩

/-- **Cartesianness of the small-étale pushforward of the sections presheaf of `𝓕`, between
affine objects of the small étale site of `Y`.**

The two halves of the comparison are read off in the shape
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_of_tmul_eq` asks for, so that nothing
here is solved for:  the equivalence comes from
`AlgebraicGeometry.SmallEtale.exists_equiv_sections_baseChange_bcMap`, which already states it at
the source of the base-change map, and the additivity and bijectivity of
`AlgebraicGeometry.SmallEtale.bcSectionsComparison` are taken from `map_add` and
`LinearEquiv.bijective` rather than from the fields of the linear equivalence, which would have to
be projected out of `Stacks.Sites.pullbackSectionsComparison` at the fibre product first. -/
public theorem isIso_restrictionBaseChange_pushforward_sections
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj U)]
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] :
    IsIso (restrictionBaseChange (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
      ((smallPushforward B a).obj
        (associatedModuleOfSections B X.obj X.property 𝓕)).val g.op) := by
  obtain ⟨ε, hεadd, hε⟩ := exists_equiv_sections_baseChange_bcMap B a 𝓕 g
  refine isIso_restrictionBaseChange_of_tmul_eq
    (Rc := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
    ((smallPushforward B a).obj
      (associatedModuleOfSections B X.obj X.property 𝓕)).val g.op
    ε hεadd
    (bcSectionsComparison B a 𝓕 g)
    (fun p q => map_add (bcSectionsComparison B a 𝓕 g) p q)
    (bcSectionsComparison B a 𝓕 g).bijective (fun b x => ?_)
  refine (restrictionBaseChange_pushforward_tmul B a 𝓕 g b x).trans ?_
  refine Eq.symm (Eq.trans ?_ (bcSectionsComparison_smul_pullbackSectionsHom B a 𝓕 g b x))
  exact congrArg _ (hε b x)

/-! ### Stacks 03LC (3) at `τ = étale` -/

/-- **The comparison of Stacks, Remark 03FH, on the two direct images, read on the underlying
presheaves of modules.**  `AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections` pushed
forward along `ε_a` and then forgotten.

Naming the forgetful image is what makes
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_pushforward_associatedModule` cheap:
the two presheaves of modules are then the ones the statement of
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_pushforward_sections` is about, on the
nose, so the hypothesis of
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso` is found without reconciling two
spellings of the same presheaf. -/
public def smallPushforwardAssociatedModuleValIso :
    ((smallPushforward B a).obj
        (associatedModuleOfSections B X.obj X.property 𝓕)).val ≅
      ((smallPushforward B a).obj
        ((associatedModule B X.obj X.property).obj 𝓕)).val :=
  (SheafOfModules.forget (structureSheaf B Y.obj Y.property)).mapIso
    ((smallPushforward B a).mapIso
      (associatedModuleIsoOfSections B X.obj X.property 𝓕).symm)

/-- **Cartesianness of the small-étale pushforward of `𝓕^a` between affine objects, read at the
associated module of Stacks 03DV rather than at the sections-defined one.**
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_pushforward_sections` transported along
`AlgebraicGeometry.SmallEtale.smallPushforwardAssociatedModuleValIso`. -/
public theorem isIso_restrictionBaseChange_pushforward_associatedModule
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj U)]
    [AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] :
    IsIso (restrictionBaseChange (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
      ((smallPushforward B a).obj
        ((associatedModule B X.obj X.property).obj 𝓕)).val g.op) :=
  have := isIso_restrictionBaseChange_pushforward_sections B a 𝓕 g
  Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso
    (R := (smallEtaleRingedSite B Y.obj Y.property).O.obj)
    (smallPushforwardAssociatedModuleValIso B a 𝓕) g.op

/-- **The base-change map of the small affine étale ringed site at a restricted module is the
base-change comparison of the small étale site**, at the image of the arrow under the inclusion of
the affine objects.  Both are the adjoint transpose of the same restriction map, the structure
presheaf of the affine site being the restriction of the one of the small étale site and the
restriction of sheaves of modules being a direct image along that inclusion.

The sheaf of modules is a *parameter*:  this identification of the two readings of one map is then
all that happens here, and a caller instantiating it solves for nothing. -/
public theorem canonicalMap_smallAffineEtaleModuleRestriction (S : Scheme.{u})
    (hS : B.Contains S) (M : SheafOfModules.{u} (structureSheaf B S hS))
    {U V : SmallAffineEtale B S hS} (g : U ⟶ V) :
    Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS)
        ((smallAffineEtaleModuleRestriction B S hS).obj M) g =
      restrictionBaseChange (R := (smallEtaleRingedSite B S hS).O.obj) M.val
        ((SmallAffineEtale.inclusion B S hS).map g).op :=
  rfl

/-- **Cartesianness on the small affine étale site from cartesianness on the small étale site**,
by `AlgebraicGeometry.SmallEtale.canonicalMap_smallAffineEtaleModuleRestriction`.  The hypothesis
is named so that a caller can pass it rather than have it searched for:  the two maps are the same
term, but instance synthesis only sees that after the base-change comparison of a ringed site is
unfolded into the adjoint transpose it abbreviates. -/
public theorem isIso_canonicalMap_smallAffineEtaleModuleRestriction (S : Scheme.{u})
    (hS : B.Contains S) (M : SheafOfModules.{u} (structureSheaf B S hS))
    {U V : SmallAffineEtale B S hS} (g : U ⟶ V)
    [hi : IsIso (restrictionBaseChange (R := (smallEtaleRingedSite B S hS).O.obj) M.val
      ((SmallAffineEtale.inclusion B S hS).map g).op)] :
    IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS)
      ((smallAffineEtaleModuleRestriction B S hS).obj M) g) := by
  rw [canonicalMap_smallAffineEtaleModuleRestriction B S hS M]
  exact hi

/-- **Cartesianness of the étale small-site pushforward of an associated module between affine
objects.**  For `f : X ⟶ Y` quasi-compact and quasi-separated, `𝓕` a quasi-coherent
`𝒪_X`-module and `U ⟶ V` a morphism of *affine* objects of the small étale site of `Y`, the
base-change map

    `Γ(V ×_Y X, p_V^*𝓕) ⊗_{Γ(V, 𝒪)} Γ(U, 𝒪) ⟶ Γ(U ×_Y X, p_U^*𝓕)`

of `f_{small, *}(𝓕^a)` is an isomorphism.  This is condition (1) of Stacks 0GZX for that
module, and it is what makes the counit of the associated-module adjunction of `Y_étale` an
isomorphism there.

The mathematics is degree-zero flat base change over an affine base,
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`, applied to
the cartesian square `AlgebraicGeometry.SmallEtale.isPullback_bcMap`;  what this file adds is
the identification of the site-theoretic base-change map with that comparison, across the two
scalar structures of
`AlgebraicGeometry.SmallEtale.isModule_pushforward_eq_baseModule`. -/
public theorem smallAffineEtale_isIso_canonicalMap_smallPushforward_associatedModule
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    ⦃U V : SmallAffineEtale B Y.obj Y.property⦄ (g : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B Y.obj Y.property)
      ((smallAffineEtaleModuleRestriction B Y.obj Y.property).obj
        ((smallPushforward B a).obj
          ((associatedModule B X.obj X.property).obj 𝓕))) g) := by
  have (W : SmallAffineEtale B Y.obj Y.property) :
      AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj
        ((SmallAffineEtale.inclusion B Y.obj Y.property).obj W)) := W.property
  exact isIso_canonicalMap_smallAffineEtaleModuleRestriction B Y.obj Y.property
    ((smallPushforward B a).obj ((associatedModule B X.obj X.property).obj 𝓕)) g
    (hi := isIso_restrictionBaseChange_pushforward_associatedModule B a 𝓕
      ((SmallAffineEtale.inclusion B Y.obj Y.property).map g))

/-- **Stacks 03LC part (3) at `τ = étale`, the second conjunct, read at an associated module.**
For `f : X ⟶ Y` quasi-compact and quasi-separated and `𝓕` a quasi-coherent `𝒪_X`-module, the
direct image `f_{small, *}(𝓕^a)` along the morphism of ringed small étale sites of
Stacks 070R (2) is quasi-coherent on `Y_étale`.

No attribute is carried:  the conjunct in full is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward`, which this statement and
Descent, Proposition 03DX (2) give.

The route is the one the source takes.  Cartesianness of the restriction of
`f_{small, *}(𝓕^a)` to the affine objects, above, makes that restriction quasi-coherent by
Stacks 0GZX (1) ⇒ (2);  `AlgebraicGeometry.SmallEtale.isIso_counit_of_affineRestriction` then
makes the counit of the associated-module adjunction of `Y_étale` an isomorphism at
`f_{small, *}(𝓕^a)`, exhibiting it as the associated module of its own restriction to the small
Zariski site of `Y`, which is quasi-coherent by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_smallPushforward_associatedModule`;
and the associated module of a quasi-coherent module is quasi-coherent on the site by
Stacks 03DV (2). -/
public theorem isQuasicoherentOnSite_smallPushforward_associatedModule
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)] :
    ((smallPushforward B a).obj
      ((associatedModule B X.obj X.property).obj 𝓕)).IsQuasicoherentOnSite :=
  have hGaff : ((smallAffineEtaleModuleRestriction B Y.obj Y.property).obj
      ((smallPushforward B a).obj
        ((associatedModule B X.obj X.property).obj 𝓕))).IsQuasicoherentOnSite :=
    smallAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B Y.obj Y.property _
      (fun {_ _} g =>
        smallAffineEtale_isIso_canonicalMap_smallPushforward_associatedModule B a 𝓕 g)
  (SheafOfModules.isQuasicoherentOnSite (structureSheaf B Y.obj Y.property)).prop_of_iso
    (@asIso _ _ _ _ _ (isIso_counit_of_affineRestriction B Y.obj Y.property _ hGaff))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B Y.obj Y.property _
      (isQuasicoherent_restrictModule_smallPushforward_associatedModule B a 𝓕))

/-- **Stacks 03LC part (3) at `τ = étale`, the second conjunct.**  For `f : X ⟶ Y` quasi-compact
and quasi-separated, the direct image `f_{small, *}` along the morphism of ringed small étale
sites of Stacks 070R (2) carries a quasi-coherent `𝒪`-module on `X_étale` to a quasi-coherent
`𝒪`-module on `Y_étale`.

The reduction to the previous statement is Descent, Proposition 03DX (2) at `τ = étale`, which
this development has unconditionally:  a quasi-coherent `𝒪`-module `𝓖` on `X_étale` restricts to
a quasi-coherent module on the affine objects by Stacks 0GZX (3) ⇒ (2), so the counit of the
associated-module adjunction of `X_étale` is an isomorphism at `𝓖` by
`AlgebraicGeometry.SmallEtale.isIso_counit_of_affineRestriction`, exhibiting `𝓖` as the
associated module of the quasi-coherent `𝒪_X`-module `ε_{X,*}𝓖`. -/
@[stacks 03LC "part (3) at τ = étale, the second conjunct: f_{small, *} carries quasi-coherent \
𝒪-modules on the small étale site of X to quasi-coherent 𝒪-modules on the small étale site of Y, \
for f quasi-compact and quasi-separated"]
public theorem isQuasicoherentOnSite_smallPushforward
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓖 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓖 : 𝓖.IsQuasicoherentOnSite) :
    ((smallPushforward B a).obj 𝓖).IsQuasicoherentOnSite := by
  have hGaff : ((smallAffineEtaleModuleRestriction B X.obj X.property).obj
      𝓖).IsQuasicoherentOnSite :=
    smallAffineEtale_isQuasicoherentOnSite_restriction B X.obj X.property 𝓖 h𝓖
  have : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf)
      ((restrictModule B X.obj X.property).obj 𝓖) :=
    isQuasicoherent_restrictModule_of_affineRestriction B X.obj X.property 𝓖 hGaff
  exact (SheafOfModules.isQuasicoherentOnSite (structureSheaf B Y.obj Y.property)).prop_of_iso
    ((smallPushforward B a).mapIso
      (@asIso _ _ _ _ _ (isIso_counit_of_affineRestriction B X.obj X.property 𝓖 hGaff)))
    (isQuasicoherentOnSite_smallPushforward_associatedModule B a
      ((restrictModule B X.obj X.property).obj 𝓖))

/-- **Stacks 03LC part (3) at `τ = étale`, the commuting square**, at one module and with no
hypothesis beyond quasi-compactness and quasi-separatedness of `f` and quasi-coherence of `𝓕`:

    `(f_*𝓕)^a ≅ f_{small, *}(𝓕^a)`.

This is `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushwardIso` with its hypothesis
discharged by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward_associatedModule`. -/
@[stacks 03LC "part (3) at τ = étale, the commuting square f_{small, *}(𝓕^a) ≅ (f_*𝓕)^a, at \
one module"]
public def associatedModuleSmallPushforwardIsoOfQcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)] :
    (associatedModule B Y.obj Y.property).obj
        ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕) ≅
      (smallPushforward B a).obj ((associatedModule B X.obj X.property).obj 𝓕) :=
  associatedModuleSmallPushforwardIso B a 𝓕
    (isQuasicoherentOnSite_smallPushforward_associatedModule B a 𝓕)

end AlgebraicGeometry.SmallEtale

end
