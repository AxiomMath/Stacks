module

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# A site is a stack in groupoids over itself

Let `(𝒞, J)` be a site. The identity functor `𝟭 𝒞` exhibits `𝒞` as a category over itself, and
this file proves that it is a stack in groupoids for every topology `J`: the fibre category over
an object `U` has `U` as its only object and the identity as its only morphism, so both descent
conditions hold with the unique available choice of glued datum.

Concretely, a morphism of `𝒞` lying over a morphism of `𝒞` for the identity functor *is* that
morphism, which is `CategoryTheory.Functor.eq_of_isHomLift_idFunctor`. Every piece of data
occurring in the `Isom` sheaf condition and in a descent datum — a chosen restriction, a gluing
isomorphism,
a canonical comparison — therefore has a prescribed value, and the two conditions reduce to
identities between composites of `eqToHom`s with the base morphisms.

## Main definitions

* `CategoryTheory.Functor.idRestriction`: the restriction of an object of `𝒞`, read through the
  identity functor, along a morphism of `𝒞`: the source of that morphism, with the morphism
  itself as cartesian lift.

## Main results

* `CategoryTheory.Functor.eq_of_isHomLift_idFunctor` and
  `CategoryTheory.Functor.eq_of_isHomLift_id_over`: a morphism lying over a morphism of the base
  for the identity functor is that morphism, read through the identifications of its source and
  target.
* `CategoryTheory.Functor.Restriction.compTo_eq_of_id`: the canonical comparison of two
  restrictions for the identity functor is the base morphism it lies over.
* `CategoryTheory.Functor.isStackInGroupoids_id`: **the identity functor is a stack in
  groupoids** for every topology on `𝒞`.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- **A morphism of `𝒞` lying over a morphism of `𝒞` for the identity functor is that
morphism.** The identity functor maps a morphism to itself, so the factorization of a lift
through its base morphism is an equality. -/
theorem eq_of_isHomLift_idFunctor {X Y : 𝒞} {m φ : X ⟶ Y} (h : (𝟭 𝒞).IsHomLift m φ) : φ = m := by
  have := h
  simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift (𝟭 𝒞) m φ).symm

/-- **A morphism of `𝒞` lies over itself for the identity functor.** -/
theorem isHomLift_id {X Y : 𝒞} (m : X ⟶ Y) : (𝟭 𝒞).IsHomLift m m :=
  CategoryTheory.IsHomLift.map (𝟭 𝒞) m

/-- **A morphism of `𝒞` lying over `m` for the identity functor is `m` read through the two
identifications of its source and target with the source and target of `m`.** -/
theorem eq_of_isHomLift_id_over {a b R T : 𝒞} {m : R ⟶ T} {φ : a ⟶ b}
    (ha : (𝟭 𝒞).obj a = R) (hb : (𝟭 𝒞).obj b = T) (h : (𝟭 𝒞).IsHomLift m φ) :
    φ = eqToHom ha ≫ m ≫ eqToHom hb.symm := by
  have := h
  exact CategoryTheory.IsHomLift.fac' (𝟭 𝒞) m φ

/-- The comparison of two identifications with the source and target of a morphism of `𝒞` lies
over that morphism, for the identity functor. -/
theorem isHomLift_idFunctor_eqToHom {a b R T : 𝒞} (ha : (𝟭 𝒞).obj a = R) (hb : (𝟭 𝒞).obj b = T)
    (m : R ⟶ T) : (𝟭 𝒞).IsHomLift m (eqToHom ha ≫ m ≫ eqToHom hb.symm) :=
  CategoryTheory.IsHomLift.of_fac' (𝟭 𝒞) m _ ha hb rfl

/-- The restriction of an object `x` of `𝒞`, read through the identity functor, along
`f : V ⟶ U`: the source `V` of `f`, with `f` itself as the cartesian lift. -/
def idRestriction {V U : 𝒞} (f : V ⟶ U) (x : 𝒞) (hx : (𝟭 𝒞).obj x = U) :
    Restriction (𝟭 𝒞) f x hx where
  pt := V
  hpt := rfl
  hom := eqToHom (rfl : (𝟭 𝒞).obj V = V) ≫ f ≫ eqToHom hx.symm
  isHomLift := isHomLift_id _
  isCart := by
    have : (𝟭 𝒞).IsHomLift (eqToHom (rfl : (𝟭 𝒞).obj V = V) ≫ f ≫ eqToHom hx.symm)
        (eqToHom (rfl : (𝟭 𝒞).obj V = V) ≫ f ≫ eqToHom hx.symm) := isHomLift_id _
    exact isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _

/-- The cartesian lift of a restriction for the identity functor is the base morphism it lies
over. -/
theorem Restriction.hom_eq_of_id {V U : 𝒞} {f : V ⟶ U} {x : 𝒞} {hx : (𝟭 𝒞).obj x = U}
    (xr : Restriction (𝟭 𝒞) f x hx) :
    xr.hom = eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm :=
  eq_of_isHomLift_idFunctor xr.isHomLift

/-- **The canonical comparison of two restrictions for the identity functor is the base morphism
it lies over.** -/
theorem Restriction.compTo_eq_of_id {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U}
    (hh : h = g ≫ f) {x : 𝒞} {hx : (𝟭 𝒞).obj x = U} (xr : Restriction (𝟭 𝒞) f x hx)
    (xrW : Restriction (𝟭 𝒞) h x hx) :
    Restriction.compTo (𝟭 𝒞) g f hh xr xrW = eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm := by
  refine eq_of_isHomLift_idFunctor ?_
  unfold Restriction.compTo
  infer_instance

/-- A morphism of the fibre category of the identity functor over `U` is the comparison of the
two identifications of its source and target with `U`. -/
theorem eq_of_fibreHom_id {U : 𝒞} {a b : 𝒞} {ha : (𝟭 𝒞).obj a = U} {hb : (𝟭 𝒞).obj b = U}
    {φ : a ⟶ b} (h : FibreHom (𝟭 𝒞) a b ha hb φ) : φ = eqToHom ha ≫ eqToHom hb.symm :=
  eq_of_isHomLift_idFunctor h

/-- **The `Isom` sheaf condition for the identity functor.** Two objects of `𝒞` identified with
one and the same `U` have exactly one fibre morphism between them, the comparison of the two
identifications, and it restricts to the given local isomorphisms because those are themselves
comparisons of identifications. -/
theorem isomIsSheafFor_id {U : 𝒞} (x y : 𝒞) (hx : (𝟭 𝒞).obj x = U) (hy : (𝟭 𝒞).obj y = U)
    {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U) (Vij : I → I → 𝒞)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction (𝟭 𝒞) (f i) x hx) (yr : ∀ i, Restriction (𝟭 𝒞) (f i) y hy)
    (xrij : ∀ i j, Restriction (𝟭 𝒞) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction (𝟭 𝒞) (pr₁ i j ≫ f i) y hy) :
    IsomIsSheafFor (𝟭 𝒞) x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hφ _ _
  refine ⟨eqToHom hx ≫ eqToHom hy.symm, ⟨isHomLift_id _, inferInstance, fun i => ?_⟩,
    fun g hg => eq_of_fibreHom_id hg.1⟩
  rw [(xr i).hom_eq_of_id, (yr i).hom_eq_of_id, eq_of_fibreHom_id (hφ i)]
  simp

/-- **Effectivity of descent data for the identity functor.** The base object `U` itself, with
the members of the covering family as its chosen restrictions, is a glued object: the comparison
isomorphisms to the given descent datum are the identifications of its objects with the members
of the family, and both the restriction relations and the gluing compatibility are identities
between composites of the base morphisms with `eqToHom`s. -/
theorem effectiveDescent_id {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)} {Vijk : I → I → I → 𝒞}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (D : DescentDatum (𝟭 𝒞) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    D.IsEffective := by
  refine ⟨U, rfl, fun i => idRestriction (f i) U rfl,
    fun i => eqToHom (idRestriction (f i) U rfl).hpt ≫ eqToHom (D.hx i).symm,
    fun i => isHomLift_id _, fun i => inferInstance, fun i j => ?_⟩
  refine ⟨idRestriction (pr₁ i j ≫ f i) U rfl,
    eqToHom (idRestriction (pr₁ i j ≫ f i) U rfl).hpt ≫ eqToHom (D.xrij i j).hpt.symm,
    eqToHom (idRestriction (pr₁ i j ≫ f i) U rfl).hpt ≫ eqToHom (D.xrji i j).hpt.symm,
    isHomLift_id _, isHomLift_id _, inferInstance, inferInstance, ?_, ?_, ?_⟩
  iterate 2
    unfold IsRestrictionOf
    rw [Restriction.compTo_eq_of_id, Restriction.compTo_eq_of_id]
    simp [Restriction.id]
  · rw [show D.φ i j = eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrji i j).hpt.symm from
      eq_of_fibreHom_id (D.φ_fibreHom i j)]
    simp

variable (𝒞) in
/-- **A site is a stack in groupoids over itself.** The fibre category of the identity functor
over an object `U` has `U` as its only object and the identity as its only morphism, so the
`Isom` sheaf condition and the effectivity of descent data both hold with the unique available
choice of glued datum, for every topology on `𝒞`. -/
theorem isStackInGroupoids_id (J : GrothendieckTopology 𝒞) :
    IsStackInGroupoids.{w} (𝟭 𝒞) J where
  isFiberedInGroupoids := isFiberedInGroupoids_id
  isom_isSheaf := by
    intro _ x y hx hy _ V f _ Vij pr₁ pr₂ hVij xr yr xrij yrij
    exact isomIsSheafFor_id x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij
  effective_descent := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D
    exact effectiveDescent_id D

end CategoryTheory.Functor

end
