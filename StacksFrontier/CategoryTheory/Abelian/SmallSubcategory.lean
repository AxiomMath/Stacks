module

public import StacksFrontier.CategoryTheory.Abelian.SmallSubcategory.AbelianOnly

/-! # Small abelian subcategories with enough injectives

Let `𝒜` be a big abelian category with enough injectives and `A : S → 𝒜` a family of
objects. There is an abelian subcategory `𝒜' ⊆ 𝒜` such that the inclusion is additive
and exact, `Ob(𝒜')` is a set, `𝒜'` contains every `A s`, `𝒜'` has enough injectives,
and an object of `𝒜'` is injective in `𝒜'` if and only if it is injective in `𝒜`.

## Main results

* `HasAbelianClosure`: the closure conditions on an object property
  `P : ObjectProperty 𝒜` that make `P.FullSubcategory` such a subcategory, namely those of
  `HasAbelianClosureCore` together with closure under injective envelopes.
* `exists_abelian_closure`: every family `A : S → 𝒜` is contained in a small object
  property satisfying `HasAbelianClosure`.
* `exists_small_abelian_subcategory_with_enough_injectives`: the full statement.

## Implementation notes

The part of the argument that does not involve injectives — the abelian structure on
`P.FullSubcategory` and the exactness of the inclusion — is in
`StacksFrontier.CategoryTheory.Abelian.SmallSubcategory.AbelianOnly`, which assumes nothing of
`𝒜` beyond being abelian; that file also documents how subcategories are described by object
properties and why the witnessing property cannot be replete. Only the two statements about
injectives, and the closure condition `closed_inj_envelope` they need, are proved here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable {S : Type w}

/-- `HasAbelianClosure P` says that the object property `P` contains a zero object and
is closed under binary biproducts, kernels, cokernels and injective envelopes — exactly
the closure properties that make `P.FullSubcategory` an abelian subcategory of `𝒜` with
enough injectives.

`P` is *not* required to be closed under arbitrary isomorphisms ("replete"), since
repleteness is incompatible with `Small.{max v w} P.FullSubcategory` in a big
category. -/
structure HasAbelianClosure (P : ObjectProperty 𝒜) : Prop extends
    HasAbelianClosureCore P where
  /-- `P` is closed under taking injective envelopes. -/
  closed_inj_envelope : ∀ X : 𝒜, P X → P (Injective.under X)

/-- Every family `A : S → 𝒜` is contained in a `max v w`-small object property with all
the closure properties of `HasAbelianClosure`. The witness is
`AbClosureConstr.generated Injective.under A`, the range of a stage-built carrier:
membership is by *equality* with a generator, `∃ g, carrier Injective.under A g = Y`,
rather than up to isomorphism, and that is what keeps `P.FullSubcategory` small. -/
theorem exists_abelian_closure (A : S → 𝒜) :
    ∃ (P : ObjectProperty 𝒜),
      HasAbelianClosure P ∧
      Small.{max v w} P.FullSubcategory ∧
      (∀ s, P (A s)) :=
  ⟨AbClosureConstr.generated Injective.under A,
    { has_zero := AbClosureConstr.has_zero Injective.under
      closed_biprod := AbClosureConstr.closed_biprod Injective.under
      closed_kernel := fun f => AbClosureConstr.closed_kernel Injective.under f
      closed_cokernel := fun f => AbClosureConstr.closed_cokernel Injective.under f
      closed_inj_envelope := AbClosureConstr.closed_unary Injective.under },
    AbClosureConstr.small_fullSubcat Injective.under A,
    AbClosureConstr.contains_A Injective.under⟩

/-- An object of `P.FullSubcategory` is injective there if and only if its underlying
object is injective in `𝒜`.

Forwards, injectivity of `X` splits the monomorphism `Injective.ι X₀ : X₀ ⟶ J₀` into the
injective envelope `J₀ = Injective.under X₀`, which lies in `P` by `closed_inj_envelope`;
so `X₀` is a retract of an injective object, hence injective. Backwards, a lifting problem
in the subcategory is pushed forward along `P.ι` — which preserves monomorphisms, being
left exact — solved in `𝒜`, and pulled back using that `P.ι` is fully faithful. -/
theorem injective_iff_of_closure {P : ObjectProperty 𝒜}
    (h : HasAbelianClosure P) (X : P.FullSubcategory) :
    Injective X ↔ Injective (P.ι.obj X) := by
  have : PreservesFiniteLimits P.ι :=
    (nonempty_preservesFiniteLimits_of_closureCore h.toHasAbelianClosureCore).some
  constructor
  · intro hX
    set X₀ := P.ι.obj X
    -- Embed `X` into its injective envelope, which again lies in `P`.
    let J : P.FullSubcategory := ⟨Injective.under X₀, h.closed_inj_envelope X₀ X.property⟩
    let ι₀' : X ⟶ J := P.ι.preimage (Injective.ι X₀)
    have hmap : P.ι.map ι₀' = Injective.ι X₀ := P.ι.map_preimage _
    have : Mono ι₀' := P.ι.mono_of_mono_map (hmap ▸ Injective.ι_mono X₀)
    -- Injectivity of `X` splits `ι₀'`, exhibiting `X₀` as a retract of `Injective.under X₀`.
    obtain ⟨r, hr⟩ := hX.factors (𝟙 X) ι₀'
    exact Retract.injective ⟨Injective.ι X₀, P.ι.map r, by
      rw [← hmap, ← P.ι.map_comp, hr, P.ι.map_id]⟩
  · intro hX₀
    refine ⟨fun {Y Z} g f _ => ?_⟩
    obtain ⟨h₀, hh₀⟩ := hX₀.factors (P.ι.map g) (P.ι.map f)
    exact ⟨P.ι.preimage h₀, P.ι.map_injective (by rw [P.ι.map_comp, P.ι.map_preimage, hh₀])⟩

/-- `P.FullSubcategory` has enough injectives: the injective envelope
`Injective.under (P.ι.obj X)` again lies in `P` by `closed_inj_envelope`, it is injective
in the subcategory by `injective_iff_of_closure`, and `Injective.ι` is a monomorphism
there because the fully faithful `P.ι` reflects monomorphisms. -/
theorem enoughInjectives_of_closure {P : ObjectProperty 𝒜}
    (h : HasAbelianClosure P) :
    EnoughInjectives P.FullSubcategory := by
  refine EnoughInjectives.mk (fun X => ⟨?_⟩)
  set X₀ := P.ι.obj X
  let J : P.FullSubcategory := ⟨Injective.under X₀, h.closed_inj_envelope X₀ X.property⟩
  let ι₀' : X ⟶ J := P.ι.preimage (Injective.ι X₀)
  have : Mono ι₀' := P.ι.mono_of_mono_map (by
    rw [P.ι.map_preimage]
    exact Injective.ι_mono X₀)
  exact { J := J, f := ι₀'
          injective := (injective_iff_of_closure h J).mpr (Injective.injective_under X₀) }

/-- **Stacks 0010**. Let `𝒜` be an abelian category with enough injectives and
`A : S → 𝒜` a family of objects. There is an object property `P` whose full subcategory
`𝒜' = P.FullSubcategory` has a set of objects, contains every `A s`, and admits an
abelian structure for which the inclusion `P.ι` is additive and exact, `𝒜'` has enough
injectives, and an object of `𝒜'` is injective there if and only if it is injective
in `𝒜`. -/
@[stacks 0010]
theorem exists_small_abelian_subcategory_with_enough_injectives (A : S → 𝒜) :
    ∃ (P : ObjectProperty 𝒜),
      Small.{max v w} P.FullSubcategory ∧
      (∀ s, P (A s)) ∧
      ∃ (_ : Abelian P.FullSubcategory),
        P.ι.Additive ∧
        Nonempty (PreservesFiniteLimits P.ι) ∧
        Nonempty (PreservesFiniteColimits P.ι) ∧
        EnoughInjectives P.FullSubcategory ∧
        ∀ X : P.FullSubcategory, Injective X ↔ Injective (P.ι.obj X) := by
  obtain ⟨P, hclos, hsmall, hA⟩ := exists_abelian_closure A
  refine ⟨P, hsmall, hA, ?_⟩
  -- Fix an abelian structure on the subcategory.
  let : Abelian P.FullSubcategory :=
    (nonempty_abelian_of_closureCore hclos.toHasAbelianClosureCore).some
  exact ⟨inferInstance, Functor.fullSubcategoryInclusion_additive P,
    nonempty_preservesFiniteLimits_of_closureCore hclos.toHasAbelianClosureCore,
    nonempty_preservesFiniteColimits_of_closureCore hclos.toHasAbelianClosureCore,
    enoughInjectives_of_closure hclos, injective_iff_of_closure hclos⟩
