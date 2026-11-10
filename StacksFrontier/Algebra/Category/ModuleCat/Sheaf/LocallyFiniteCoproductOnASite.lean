module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Topology.Sheaves.LocallyFiniteCoproductSections

/-!
# A locally finitely supported coproduct of sheaves of modules is a product

Let `R` be a sheaf of rings on a site `(C, J)` and let `M : I → SheafOfModules R` be a family of
sheaves of modules indexed by a type `I : Type`. Call the family *locally finitely supported* if
every object `V` of `C` carries a covering sieve on whose members all but finitely many of the
`M i` restrict to the zero sheaf of modules. For such a family the canonical comparison
`∐ M ⟶ ∏ᶜ M` is an isomorphism: the coproduct of the family is also its product.

The reason is the one behind Tag 02FT for a locally finite open covering of a space. The
coproduct of a family of sheaves of modules is the sheafification of the coproduct taken in
presheaves of modules, and the latter is computed objectwise; over an object `W` on which all but
finitely many `M i` vanish, a direct sum of modules with only finitely many nonzero summands is
already their product. So the comparison morphism of presheaves from the objectwise coproduct to
the sections of `∏ᶜ M` is an isomorphism over each member of the covering, hence locally
bijective, hence an isomorphism after sheafification.

The two consequences at the end are what a consumer needs: a morphism into `∐ M` may be
prescribed by its components and is determined by them. The components are passed as data,
characterized by being the identity on their own summand and zero on the others, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoproductSheafification.lean`; a consumer whose
projections are, say, `CategoryTheory.GradedObject.Monoidal.πTensorObj` therefore needs no lemma
identifying its spelling of a projection with `CategoryTheory.Limits.Sigma.π`.

## Main definitions

* `Stacks.SheafOfModules.CoproductSheafification.IsLocallyFinitelySupported`: every object of the
  site has a covering on whose members all but finitely many members of the family restrict to
  zero.
* `Stacks.SheafOfModules.CoproductSheafification.deltaInj`: the canonical injection of `M i` into
  `∏ᶜ M`, the identity in the `i`-th factor and zero in the others.
* `Stacks.SheafOfModules.CoproductSheafification.coprodToProd`: the canonical comparison
  `∐ M ⟶ ∏ᶜ M`.
* `Stacks.SheafOfModules.CoproductSheafification.presToProd`: the comparison from the objectwise
  coproduct of the underlying presheaves of modules to the sections of `∏ᶜ M`.

## Main results

* `Stacks.SheafOfModules.CoproductSheafification.isIso_presToProd_app`: over an object on which
  all but finitely many members of the family vanish, `presToProd` is an isomorphism.
* `Stacks.SheafOfModules.CoproductSheafification.isIso_coprodToProd`: **for a locally finitely
  supported family the canonical comparison `∐ M ⟶ ∏ᶜ M` is an isomorphism.**
* `Stacks.SheafOfModules.CoproductSheafification.exists_hom_comp_eq`: **a morphism into `∐ M` can
  be prescribed by its components.**
* `Stacks.SheafOfModules.CoproductSheafification.hom_ext_of_comp_eq`: **a morphism into `∐ M` is
  determined by its components.**
* `Stacks.SheafOfModules.CoproductSheafification.coprodToProd_comp_π_eq`: any family of
  components in the above sense is recovered from `coprodToProd` by composing with the
  projections of the product. This holds with no finiteness hypothesis whatever, and is what
  lets the two deliverables be stated for abstract components.

## Implementation notes

The index type is `Type 0`, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoproductSheafification.lean`, whose
implementation notes explain why: the finiteness statements there run through `⨁ i, Z i`, and
fixing the index universe at `0` avoids inverting `max`. Here the restriction is inherited rather
than needed for its own sake, but it also makes `Small.{u} (Discrete I)` — the hypothesis of
`CategoryTheory.SheafOfModules.hasLimitsOfShape`, which is what makes `∏ᶜ M` exist — available by
instance search with nothing to supply by hand.

`IsLocallyFinitelySupported` is stated in a section in which the sheaf of rings is implicit, so
that it reads `IsLocallyFinitelySupported M`; everything else keeps the explicit `R` of the
ambient file, so the deliverables read `exists_hom_comp_eq R M h π hself hzero f`.

`DecidableEq I` is needed to *write down* `deltaInj` and hence `coprodToProd`, but neither of the
two deliverables mentions them, so it is omitted from their statements and recovered inside their
proofs by `classical`. This is what the `unusedDecidableInType` linter asks for, and it leaves
the deliverables applicable to a family indexed by a type with no decidable equality.

The vanishing hypothesis is `IsZero ((M i).over W)`, the restriction of `M i` to the slice site
over `W` being a zero object, because that is the shape in which a consumer meets it. What the
objectwise argument needs is only that the sections over `W` itself vanish, and
`Stacks.SheafOfModules.CoproductSheafification.isZero_val_obj_of_isZero_over` crosses the gap:
`Stacks.subsingleton_of_isZero` applied to the object `Over.mk (𝟙 W)` of the slice site gives a
subsingleton whose carrier is, definitionally, the sections of `M i` over `W`, because
`CategoryTheory.PresheafOfModules.pushforward` does not change the underlying type.

Local bijectivity of `presToProd` is read off a single fact, that `presToProd` is an isomorphism
over every member of the covering, via `Stacks.isIso_of_isZero_of_notMem`; this is the packaging
recommended by the topological analogue, where it is used in the same way. Local bijectivity of
the comparison of *sheaves* is then obtained by cancelling `toCoprod` from
`toCoprod ≫ (coprodToProd).val = presToProd`, using that `toCoprod` is locally surjective
(`Stacks.SheafOfModules.CoproductSheafification.isLocallySurjective_toCoprod`): no sheafification
functor and no adjunction transpose appears, which avoids having to identify
`Stacks.FreeSheafification.shf` with `CategoryTheory.PresheafOfModules.sheafification (𝟙 R.obj)`.

Finally `coprodToProd_comp_π_eq` deserves emphasis: `coprodToProd R M ≫ Pi.π M i = π i` for *any*
family of components satisfying the two characterizing equations, with no hypothesis on the
family. So the only use of `isIso_coprodToProd` in the two deliverables is to invert, resp. to
cancel, `coprodToProd` itself.

## References

* [Stacks Project, Tag 02FT](https://stacks.math.columbia.edu/tag/02FT) — the analogue for a
  locally finite open covering of a topological space, formalized in
  `StacksFrontier/Topology/Sheaves/LocallyFiniteCoproductSections.lean`.
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

namespace Stacks.SheafOfModules.CoproductSheafification

universe v u u'

/-! ### Locally finitely supported families -/

section Support

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {I : Type} (M : I → SheafOfModules.{u} R)

/-- Every object of the site has a covering on whose members all but finitely many members of
the family restrict to zero. -/
def IsLocallyFinitelySupported : Prop :=
  ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
    ∃ S : Finset I, ∀ i ∉ S, IsZero ((M i).over W)

end Support

/-! ### The comparison from the coproduct to the product -/

section Comparison

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  {I : Type} [DecidableEq I] (M : I → SheafOfModules.{u} R)

/-- The canonical injection of `M i` into the product `∏ᶜ M`: its `j`-th component is the
identity for `j = i` and zero otherwise. -/
def deltaInj (i : I) : M i ⟶ ∏ᶜ M :=
  Pi.lift fun j => if h : i = j then eqToHom (congrArg M h) else 0

/-- The `i`-th component of the `i`-th canonical injection is the identity. -/
@[simp]
theorem deltaInj_comp_π_self (i : I) : deltaInj R M i ≫ Pi.π M i = 𝟙 (M i) := by
  rw [deltaInj, Pi.lift_comp_π]
  simp

/-- The `j`-th component of the `i`-th canonical injection vanishes for `j ≠ i`. -/
@[simp]
theorem deltaInj_comp_π_ne {i j : I} (h : i ≠ j) : deltaInj R M i ≫ Pi.π M j = 0 := by
  rw [deltaInj, Pi.lift_comp_π]
  simp [h]

/-- The comparison morphism of presheaves of modules from the objectwise coproduct of the
underlying presheaves to the sections of the product `∏ᶜ M`. Over an object `W` it is the
inclusion of the direct sum of the modules `(M i) (W)` into their product. -/
def presToProd : presCoprod R M ⟶ (∏ᶜ M).val :=
  Sigma.desc fun i => (deltaInj R M i).val

/-- The `i`-th leg of the objectwise coproduct, followed by the comparison morphism, is the
`i`-th canonical injection. -/
theorem ι_presToProd (i : I) :
    Sigma.ι (fun k => (M k).val) i ≫ presToProd R M = (deltaInj R M i).val :=
  Sigma.ι_comp_desc _ _

/-- The `i`-th leg of the objectwise coproduct, followed by the comparison morphism and the
`i`-th projection, is the identity. -/
theorem ι_presToProd_comp_π_self (i : I) :
    Sigma.ι (fun k => (M k).val) i ≫ presToProd R M ≫ (Pi.π M i).val = 𝟙 ((M i).val) := by
  rw [← Category.assoc, ι_presToProd]
  exact congrArg SheafOfModules.Hom.val (deltaInj_comp_π_self R M i)

/-- The `i`-th leg of the objectwise coproduct, followed by the comparison morphism and the
`j`-th projection, vanishes for `j ≠ i`. -/
theorem ι_presToProd_comp_π_ne {i j : I} (h : i ≠ j) :
    Sigma.ι (fun k => (M k).val) i ≫ presToProd R M ≫ (Pi.π M j).val = 0 := by
  rw [← Category.assoc, ι_presToProd]
  exact congrArg SheafOfModules.Hom.val (deltaInj_comp_π_ne R M h)

/-- A sheaf of modules whose restriction to the slice site over `W` is a zero object has no
nonzero sections over `W`. -/
theorem isZero_val_obj_of_isZero_over {N : SheafOfModules.{u} R} {W : C}
    (h : IsZero (N.over W)) : IsZero (N.val.obj (op W)) := by
  have h2 := Stacks.subsingleton_of_isZero h (op (Over.mk (𝟙 W)))
  exact @ModuleCat.isZero_of_subsingleton _ _ _ h2

/-- **The algebraic heart.** If all but finitely many members of the family have no nonzero
sections over `W`, then the comparison morphism is an isomorphism over `W`: a direct sum and a
product of a family of modules with only finitely many nonzero members agree. -/
theorem isIso_presToProd_app (W : C) (S : Finset I)
    (hS : ∀ i ∉ S, IsZero ((M i).val.obj (op W))) :
    IsIso ((presToProd R M).app (op W)) := by
  have hc := isColimitOfHasCoproductOfPreservesColimit
    (PresheafOfModules.evaluation R.obj (op W)) (fun i => (M i).val)
  have hl := isLimitOfPreserves (SheafOfModules.evaluation.{u} R (op W)) (productIsProduct M)
  refine Stacks.isIso_of_isZero_of_notMem
    (A := fun i => (M i).val.obj (op W))
    (fun i => (Sigma.ι (fun k => (M k).val) i).app (op W))
    (fun i => (Pi.π M i).val.app (op W))
    (fun g h hgh => Cofan.IsColimit.hom_ext hc g h hgh)
    (fun g h hgh => hl.hom_ext (by rintro ⟨i⟩; exact hgh i))
    _ (fun i => ?_) (fun i j hij => ?_) S hS
  · exact congrArg (fun φ : (M i).val ⟶ (M i).val => φ.app (op W))
      (ι_presToProd_comp_π_self R M i)
  · exact congrArg (fun φ : (M i).val ⟶ (M j).val => φ.app (op W))
      (ι_presToProd_comp_π_ne R M hij)

/-! ### Local bijectivity of the comparison of presheaves -/

/-- For a locally finitely supported family, every object of the site carries a covering sieve on
whose members the comparison morphism of presheaves is an isomorphism. -/
theorem exists_sieve_isIso_presToProd_app (h : IsLocallyFinitelySupported M) (V : C) :
    ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃W : C⦄ (g : W ⟶ V), T g → IsIso ((presToProd R M).app (op W)) := by
  obtain ⟨T, hT, hfin⟩ := h V
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S, hS⟩ := hfin g hg
  exact isIso_presToProd_app R M W S fun i hi => isZero_val_obj_of_isZero_over R (hS i hi)

/-- Where the comparison morphism of presheaves is an isomorphism, the underlying map of abelian
groups is bijective. -/
theorem bijective_toPresheaf_presToProd_app {W : C}
    (hiso : IsIso ((presToProd R M).app (op W))) :
    Function.Bijective
      (((PresheafOfModules.toPresheaf R.obj).map (presToProd R M)).app (op W)) :=
  ConcreteCategory.bijective_of_isIso ((presToProd R M).app (op W))

/-- **The comparison morphism of presheaves is locally injective**, being an isomorphism over
every member of a covering sieve. -/
theorem isLocallyInjective_presToProd (h : IsLocallyFinitelySupported M) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (presToProd R M)) where
  equalizerSieve_mem {V} x y hxy := by
    obtain ⟨T, hT, hiso⟩ := exists_sieve_isIso_presToProd_app R M h V.unop
    refine J.superset_covering ?_ hT
    intro W g hg
    refine (bijective_toPresheaf_presToProd_app R M (hiso g hg)).1 ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- **The comparison morphism of presheaves is locally surjective**, being an isomorphism over
every member of a covering sieve. -/
theorem isLocallySurjective_presToProd (h : IsLocallyFinitelySupported M) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (presToProd R M)) where
  imageSieve_mem {V} s := by
    obtain ⟨T, hT, hiso⟩ := exists_sieve_isIso_presToProd_app R M h V
    refine J.superset_covering ?_ hT
    intro W g hg
    exact (bijective_toPresheaf_presToProd_app R M (hiso g hg)).2 _

/-! ### The comparison of sheaves -/

variable [HasCoproduct M]

/-- **The canonical comparison from the coproduct to the product**: the morphism whose
`(i, j)`-component is the identity for `i = j` and zero otherwise. -/
def coprodToProd : (∐ M) ⟶ ∏ᶜ M :=
  Sigma.desc (deltaInj R M)

/-- The `(i, j)`-component of the canonical comparison. -/
theorem ι_coprodToProd_comp_π (i j : I) :
    Sigma.ι M i ≫ coprodToProd R M ≫ Pi.π M j =
      if h : i = j then eqToHom (congrArg M h) else 0 := by
  rw [← Category.assoc, coprodToProd, Sigma.ι_comp_desc, deltaInj, Pi.lift_comp_π]

/-- **Any family of components of `∐ M` is recovered from the canonical comparison.** If
`π i : ∐ M ⟶ M i` is the identity on the `i`-th summand and zero on the others — which is how a
consumer supplies the components it already has — then `π i` is the canonical comparison followed
by the `i`-th projection of the product. No finiteness hypothesis is needed. -/
theorem coprodToProd_comp_π_eq (π : ∀ i, (∐ M) ⟶ M i)
    (hself : ∀ i, Sigma.ι M i ≫ π i = 𝟙 (M i))
    (hzero : ∀ i j, j ≠ i → Sigma.ι M j ≫ π i = 0) (i : I) :
    coprodToProd R M ≫ Pi.π M i = π i := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [ι_coprodToProd_comp_π]
  by_cases hji : j = i
  · subst hji
    rw [hself]
    simp
  · rw [hzero i j hji]
    simp [hji]

/-- The canonical morphism from the objectwise coproduct to the presheaf underlying `∐ M`,
followed by the comparison of sheaves, is the comparison of presheaves. -/
theorem toCoprod_comp_val_coprodToProd :
    toCoprod R M ≫ (coprodToProd R M).val = presToProd R M := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, ι_toCoprod, ι_presToProd]
  exact congrArg SheafOfModules.Hom.val (Sigma.ι_comp_desc (deltaInj R M) i)

end Comparison

/-! ### The isomorphism and its two consequences -/

section Main

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {I : Type} [DecidableEq I] (M : I → SheafOfModules.{u} R) [HasCoproduct M]

/-- **For a locally finitely supported family the canonical comparison from the coproduct to the
product is an isomorphism**: the coproduct `∐ M` is also the product `∏ᶜ M`.

The comparison of presheaves is locally bijective, and the canonical morphism from the objectwise
coproduct to the presheaf underlying `∐ M` is locally surjective, so the comparison of sheaves is
locally bijective; a locally bijective morphism of sheaves of abelian groups is an isomorphism,
and `CategoryTheory.SheafOfModules.toSheaf` reflects isomorphisms. -/
theorem isIso_coprodToProd (h : IsLocallyFinitelySupported M) : IsIso (coprodToProd R M) := by
  have := isLocallyInjective_presToProd R M h
  have := isLocallySurjective_presToProd R M h
  have := isLocallySurjective_toCoprod R M
  have hfac : (PresheafOfModules.toPresheaf R.obj).map (toCoprod R M) ≫
      (PresheafOfModules.toPresheaf R.obj).map (coprodToProd R M).val =
      (PresheafOfModules.toPresheaf R.obj).map (presToProd R M) := by
    rw [← Functor.map_comp]
    exact congrArg (PresheafOfModules.toPresheaf R.obj).map (toCoprod_comp_val_coprodToProd R M)
  have h1 : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (coprodToProd R M).val) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have h2 : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (coprodToProd R M).val) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J _ hfac
  have : IsIso ((SheafOfModules.toSheaf.{u} R).map (coprodToProd R M)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨h2, h1⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u} R)

omit [DecidableEq I] in
/-- **A morphism into a locally finitely supported coproduct may be prescribed by its
components.** Given a family `f i : T ⟶ M i` there is a morphism `u : T ⟶ ∐ M` whose `i`-th
component is `f i`.

As in `Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_ι`, the components
of `∐ M` are given as data characterized by the two equations the canonical ones satisfy, so a
consumer passes the components it already has — for a graded tensor product,
`CategoryTheory.GradedObject.Monoidal.πTensorObj` together with `ιTensorObj_πTensorObj_self` and
`ιTensorObj_πTensorObj_ne` — and no identification of two spellings of one projection is
needed. -/
theorem exists_hom_comp_eq (h : IsLocallyFinitelySupported M) {T : SheafOfModules.{u} R}
    (π : ∀ i, (∐ M) ⟶ M i)
    (hself : ∀ i, Sigma.ι M i ≫ π i = 𝟙 (M i))
    (hzero : ∀ i j, j ≠ i → Sigma.ι M j ≫ π i = 0)
    (f : ∀ i, T ⟶ M i) : ∃ u : T ⟶ ∐ M, ∀ i, u ≫ π i = f i := by
  classical
  have := isIso_coprodToProd R M h
  refine ⟨Pi.lift f ≫ inv (coprodToProd R M), fun i => ?_⟩
  rw [Category.assoc, ← coprodToProd_comp_π_eq R M π hself hzero i,
    IsIso.inv_hom_id_assoc, Pi.lift_comp_π]

omit [DecidableEq I] in
/-- **A morphism into a locally finitely supported coproduct is determined by its components.**
The components are given as data, characterized exactly as in
`Stacks.SheafOfModules.CoproductSheafification.exists_hom_comp_eq`. -/
theorem hom_ext_of_comp_eq (h : IsLocallyFinitelySupported M) {T : SheafOfModules.{u} R}
    (π : ∀ i, (∐ M) ⟶ M i)
    (hself : ∀ i, Sigma.ι M i ≫ π i = 𝟙 (M i))
    (hzero : ∀ i j, j ≠ i → Sigma.ι M j ≫ π i = 0)
    (u v : T ⟶ ∐ M) (huv : ∀ i, u ≫ π i = v ≫ π i) : u = v := by
  classical
  have := isIso_coprodToProd R M h
  refine (cancel_mono (coprodToProd R M)).1 (Pi.hom_ext _ _ fun i => ?_)
  rw [Category.assoc, Category.assoc, coprodToProd_comp_π_eq R M π hself hzero i, huv]

end Main

end Stacks.SheafOfModules.CoproductSheafification

end

end

