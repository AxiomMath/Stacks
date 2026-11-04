module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import StacksFrontier.AlgebraicGeometry.Flatness.ModuleMapBaseChange

/-!
# The zero-after-base-change functor on a cofiltered inverse system of affine schemes

Let `f : X ⟶ S` be a morphism of schemes and `u : F ⟶ G` a homomorphism of quasi-coherent
modules on `X`.  `Stacks.Flatness.ModuleMapBaseChangeSituation.zeroFunctor` is the subterminal
functor on `(Over S)ᵒᵖ` whose value at `T` records whether the base change `u_T` on `X ×_S T`
is zero.  [Stacks, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ) asserts, when `f` is
quasi-compact and `F` is of finite type, that this functor is *limit preserving*: it carries
the inverse limit of a cofiltered system of affine schemes over `S` to the corresponding
filtered colimit of sets, which is `CategoryTheory.Limits.PreservesColimit` for the opposite
diagram.

This file separates that assertion into its two independent halves.

The first half is categorical and is proved here in full generality.  All the values of the
three functors of Tag 05MH are subsingletons, and the opposite of a cofiltered category is
filtered; for such a functor and such a diagram, *the whole of colimit preservation is the
single implication "the value at the limit is inhabited only if some value along the diagram
is"*.  Nothing else survives: the comparison map out of the filtered colimit is automatically
injective because a filtered colimit of subsingletons is a subsingleton, and the universal
property has no further content because all the maps in sight are determined on a
subsingleton.  `Stacks.Flatness.preservesColimit_of_subsingleton` is this reduction.

The second half is the geometric descent statement itself, and it is *not* proved here: it is
carried as the explicit hypothesis `hdesc` of
`zeroFunctor_preservesColimit_of_isAffine_of_descent` in the namespace
`Stacks.Flatness.ModuleMapBaseChangeSituation`.  Its ring-level core is already available in
this repository as
`Stacks.Flattening.exists_lTensor_eq_zero_of_directed`
(`StacksFrontier/RingTheory/Flat/ZeroFunctorLimit.lean`), which says that the vanishing of a base
change `T ⊗_A M ⟶ T ⊗_A N` of a homomorphism with finitely generated source descends to a
member of any directed family of `A`-subalgebras exhausting `T`.  What stands between that and
`hdesc` is the passage from the inverse limit of affine schemes over `S` to the directed
colimit of their rings of sections, and the reduction of the vanishing of a homomorphism of
quasi-coherent modules on `X ×_S T` to a finite affine cover, which is where quasi-compactness
of `f` and finite type of `F` enter.

## Main results

* `Stacks.Flatness.isColimitOfSubsingleton`: a cocone over a filtered diagram of subsingletons
  with subsingleton vertex is a colimit as soon as inhabitedness of the vertex is witnessed
  somewhere along the diagram.
* `Stacks.Flatness.preservesColimit_of_subsingleton`: hence a functor to `Type` with
  subsingleton values preserves the colimit of a filtered diagram as soon as that same
  implication holds at every colimit cocone.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.isZeroAfterBaseChange_congr`: the zero
  condition depends only on the isomorphism class of the scheme over the base.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.zeroFunctor_preservesColimit_of_isLimit`: the
  descent hypothesis need only be checked at one chosen model of the inverse limit.
* `zeroFunctor_preservesColimit_of_isAffine_of_descent`, in the namespace
  `Stacks.Flatness.ModuleMapBaseChangeSituation`, is Tag 05MJ for the zero condition,
  conditional on the geometric descent hypothesis.  It
  states it for an index category in an arbitrary universe, which is why that hypothesis is
  carried: the unconditional
  `Stacks.Flatness.ModuleMapBaseChangeSituation.zeroFunctor_preservesColimit_of_isAffine`
  of `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.ZeroLimit` discharges it at the
  cost of restricting the index category to the universe of the schemes.

## Implementation notes

`CategoryTheory.Limits.IsColimit` is data, not a proposition, so `isColimitOfSubsingleton` is a
`noncomputable def`: the descent hypothesis is an existential statement and the colimit
comparison map is built by choosing a witness from it.  This costs nothing downstream, since
the only consumer is the `Prop`-valued class `CategoryTheory.Limits.PreservesColimit`.

The route to the descent hypothesis does *not* need a module-level version of
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`.  On an affine open of `X ×_S T` whose
preimages in the system are affine, `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`
turns the sections of the pulled-back module into `B_∞ ⊗_{B} M`, where `B_∞` is the ring of
sections at the limit; that ring is the filtered colimit of the rings of sections at the stages
by the structure-sheaf statement already in Mathlib, and the vanishing then descends by
`Stacks.Flattening.exists_adjoin_lTensor_eq_zero`.  Quasi-compactness of `f` makes the affine
cover of `X ×_S T` finite, so the finitely many stages so produced can be combined by
cofilteredness, and finite type of `F` supplies `Module.Finite` on each piece.  Note that the
index category here is `I : Type v` with `Category.{w} I` and carries no smallness hypothesis,
whereas Mathlib's cofiltered-limit results require `I : Type u` with `Category.{u} I`; the
universe-free restatements, of which
`AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit_of_initiallySmall` is the one in point,
need `CategoryTheory.LocallySmall.{u} I` and `CategoryTheory.InitiallySmall.{u} I`, so either
those hypotheses must be added or the descent must be proved by hand for a large index
category.

The descent hypothesis is stated over a `CategoryTheory.Limits.Cone` of the original diagram
rather than over a `CategoryTheory.Limits.Cocone` of its opposite, so that a future proof of it
can be written about an honest inverse limit of schemes over `S`.  The translation is
`CategoryTheory.Limits.isLimitConeUnopOfCocone`, and `(T.op).unop` is `T` on the nose, so no
comparison isomorphism intervenes.

## References

* [Stacks Project, Tag 05MH](https://stacks.math.columbia.edu/tag/05MH)
* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe t w v u₁ v₁ u

namespace Stacks.Flatness

/-- Any two sections of a cocone over a filtered diagram of subsingleton types agree: push both
to a common stage, where there is only one element. -/
theorem cocone_app_eq_of_subsingleton {J : Type v} [Category.{w} J] [IsFiltered J]
    {G : J ⥤ Type t} (hG : ∀ j, Subsingleton (G.obj j)) (s : Cocone G)
    {j₁ j₂ : J} (g₁ : G.obj j₁) (g₂ : G.obj j₂) : s.ι.app j₁ g₁ = s.ι.app j₂ g₂ := by
  have h₁ := ConcreteCategory.congr_hom (s.w (IsFiltered.leftToMax j₁ j₂)) g₁
  have h₂ := ConcreteCategory.congr_hom (s.w (IsFiltered.rightToMax j₁ j₂)) g₂
  simp only [types_comp_apply] at h₁ h₂
  rw [← h₁, ← h₂, (hG (IsFiltered.max j₁ j₂)).elim (G.map (IsFiltered.leftToMax j₁ j₂) g₁)
    (G.map (IsFiltered.rightToMax j₁ j₂) g₂)]

/-- A cocone over a filtered diagram of subsingleton types whose vertex is a subsingleton is a
colimit cocone as soon as an element of the vertex forces an element somewhere along the
diagram.

Both directions of the universal property reduce to
`Stacks.Flatness.cocone_app_eq_of_subsingleton`: the comparison map into a competing cocone can
only be "evaluate at some stage where the diagram is inhabited", and any two such choices
agree. -/
noncomputable def isColimitOfSubsingleton {J : Type v} [Category.{w} J] [IsFiltered J]
    {G : J ⥤ Type t} (d : Cocone G) (hG : ∀ j, Subsingleton (G.obj j))
    (hpt : Subsingleton d.pt) (hd : Nonempty d.pt → ∃ j, Nonempty (G.obj j)) :
    IsColimit d where
  desc s := ↾fun x ↦ s.ι.app (hd ⟨x⟩).choose (hd ⟨x⟩).choose_spec.some
  fac s j := by
    ext g
    exact cocone_app_eq_of_subsingleton hG s _ g
  uniq s m hm := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, TypeCat.ofHom_apply]
    obtain ⟨j, hj⟩ := hd ⟨x⟩
    have hx : x = d.ι.app j hj.some := hpt.elim _ _
    rw [hx]
    have h := ConcreteCategory.congr_hom (hm j) hj.some
    simp only [types_comp_apply] at h
    rw [h]
    exact cocone_app_eq_of_subsingleton hG s _ _

/-- A functor to `Type` all of whose values are subsingletons preserves the colimit of a
filtered diagram as soon as, at every colimit cocone, inhabitedness of the value at the
colimit is witnessed somewhere along the diagram.

This is the whole categorical content of "a subterminal functor is limit preserving": the
remaining obligation is the single implication `hdesc`. -/
theorem preservesColimit_of_subsingleton {J : Type v} [Category.{w} J] [IsFiltered J]
    {C : Type u₁} [Category.{v₁} C] (K : J ⥤ C) (F : C ⥤ Type t)
    (hF : ∀ X, Subsingleton (F.obj X))
    (hdesc : ∀ c : Cocone K, IsColimit c → Nonempty (F.obj c.pt) →
      ∃ j, Nonempty (F.obj (K.obj j))) :
    PreservesColimit K F where
  preserves {c} hc :=
    ⟨isColimitOfSubsingleton (F.mapCocone c) (fun _ ↦ hF _) (hF _) (hdesc c hc)⟩

namespace ModuleMapBaseChangeSituation

/-- Every value of the zero functor is a subsingleton: it is a `PLift` of a proposition. -/
instance zeroFunctor_obj_subsingleton (D : ModuleMapBaseChangeSituation.{u})
    (T : (Over D.S)ᵒᵖ) : Subsingleton (D.zeroFunctor.obj T) :=
  inferInstanceAs (Subsingleton (PLift (D.IsZeroAfterBaseChange T.unop)))

/-- The zero functor has a section over `T` exactly when the base-changed homomorphism is
zero. -/
@[simp]
theorem zeroFunctor_obj_nonempty_iff (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) :
    Nonempty (D.zeroFunctor.obj (Opposite.op T)) ↔ D.IsZeroAfterBaseChange T :=
  ⟨fun ⟨⟨h⟩⟩ ↦ h, fun h ↦ ⟨⟨h⟩⟩⟩

/-- Being zero after base change only depends on the isomorphism class of the scheme over the
base.  Together with `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso` this lets the
descent hypothesis below be checked at any single chosen model of the inverse limit. -/
theorem isZeroAfterBaseChange_congr (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}
    (e : T ≅ T') : D.IsZeroAfterBaseChange T ↔ D.IsZeroAfterBaseChange T' :=
  ⟨D.isZeroAfterBaseChange_of_hom e.inv, D.isZeroAfterBaseChange_of_hom e.hom⟩

/-- The zero functor preserves the colimit of the opposite of a cofiltered diagram as soon as the
descent statement holds at every inverse limit of that diagram. -/
private theorem zeroFunctor_preservesColimit_of_forall_isLimit
    (D : ModuleMapBaseChangeSituation.{u}) (I : Type v) [Category.{w} I] [IsCofiltered I]
    (T : I ⥤ Over D.S)
    (hdesc : ∀ c : Cone T, IsLimit c → D.IsZeroAfterBaseChange c.pt →
      ∃ i, D.IsZeroAfterBaseChange (T.obj i)) :
    PreservesColimit T.op D.zeroFunctor := by
  refine preservesColimit_of_subsingleton T.op D.zeroFunctor (fun X ↦ inferInstance)
    (fun c hc h ↦ ?_)
  obtain ⟨i, hi⟩ := hdesc c.unop (isLimitConeUnopOfCocone T.op hc) h.some.down
  exact ⟨Opposite.op i, ⟨⟨hi⟩⟩⟩

/-- The zero functor preserves the colimit of the opposite of a cofiltered diagram as soon as
the descent statement holds at **one** chosen inverse limit of that diagram: all inverse limits
of the diagram are isomorphic over the base, and `isZeroAfterBaseChange_congr` transports the
conclusion between them.

This is the form in which the descent statement should be attacked, since it may be proved for
a concrete model of the limit — for instance the `Spec` of the directed colimit of the rings of
sections, when the members of the diagram are affine. -/
theorem zeroFunctor_preservesColimit_of_isLimit (D : ModuleMapBaseChangeSituation.{u})
    (I : Type v) [Category.{w} I] [IsCofiltered I] (T : I ⥤ Over D.S)
    (c : Cone T) (hc : IsLimit c)
    (hdesc : D.IsZeroAfterBaseChange c.pt → ∃ i, D.IsZeroAfterBaseChange (T.obj i)) :
    PreservesColimit T.op D.zeroFunctor :=
  zeroFunctor_preservesColimit_of_forall_isLimit D I T fun _ hc' h ↦
    hdesc ((D.isZeroAfterBaseChange_congr (hc'.conePointUniqueUpToIso hc)).1 h)

/-- **Stacks Project, Tag 05MJ, the zero condition.** For a quasi-compact `f : X ⟶ S` and a
homomorphism of quasi-coherent modules with source of finite type, the functor recording where
the base change of the homomorphism is zero carries the inverse limit of a cofiltered system of
affine schemes over `S` to the filtered colimit of its values.

The hypothesis `hdesc` is the geometric descent statement and is the one thing not proved here:
if the base change of the homomorphism to the inverse limit of the system is zero, then its
base change to one of the members of the system is already zero.  Everything else in the
assertion — the construction of the comparison map out of the filtered colimit, its
injectivity, and the universal property — is supplied by
`Stacks.Flatness.preservesColimit_of_subsingleton`. -/
theorem zeroFunctor_preservesColimit_of_isAffine_of_descent
    (D : ModuleMapBaseChangeSituation.{u}) [QuasiCompact D.f] [D.F.IsFiniteType]
    (I : Type v) [Category.{w} I] [IsCofiltered I]
    (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left)
    (hdesc : ∀ c : Cone T, IsLimit c → D.IsZeroAfterBaseChange c.pt →
      ∃ i, D.IsZeroAfterBaseChange (T.obj i)) :
    PreservesColimit T.op D.zeroFunctor := by
  have _ := hT
  exact zeroFunctor_preservesColimit_of_forall_isLimit D I T hdesc

end ModuleMapBaseChangeSituation

end Stacks.Flatness

end
