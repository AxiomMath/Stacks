module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedDescAlongPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedFibreBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres

/-!
# The composition clause of Stacks 0GIX: the left-hand side in normal form

Let `f : X ⟶ S` be a morphism of schemes and `s` a geometric point of `S`. The last sentence of
Stacks 0GIX asserts that the composite of its two canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

is the derived base change map of the cartesian square defining the geometric fibre. The statement
of that clause is displayed in the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedFibreBaseChangeComposition.lean`; this file carries out the left-hand
half of its proof and assembles the two components of the right-hand half which the library did
not record.

Both sides of the clause are transformations out of the right derived functor
`Rf_* ⋙ (-)_s`, so `CategoryTheory.Functor.rightDerived_ext` reduces the clause to an equality of
components at a complex `J` of abelian sheaves on the small étale site of `X`. What is proved here
is that the left-hand component has the normal form

`(-)_s-factorization ≫ Qh(degreewise composite) ≫ RΓ(X_s)-unit ≫ RΓ(X_s)(q⁻¹-factorization)`,

in which the degreewise composite is the map on sheaves
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` followed by restriction of
global sections to the geometric fibre. That is
`AlgebraicGeometry.stalkSectionsUnit_comp_fibreSections_app`.

## Main results

* `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three` — a three-step degreewise
  composite on homotopy categories is the degreewise action of the composite transformation.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso_inv` —
  the comparison of the degreewise actions of two isomorphic exact functors, read against the
  inverses of both the factorizations through the homotopy category and the comparison itself.
* the same for the two inverse images of abelian étale sheaves, as
  `Stacks.EtaleCohomology`'s `...comp_smallEtaleDerivedPullbackAbIso_inv`, which is the direction
  in which the derived base change map of Stacks 0A2A leaves the étale-abelian vocabulary.
* `CategoryTheory.Functor.mapDerivedCategoryFactorsh_inv_comp_mapDerivedCategoryCompIso_hom` — the
  composition isomorphism of two exact functors on the image of `DerivedCategory.Qh`, with the two
  factorizations of the composed actions cancelled.
* `AlgebraicGeometry.stalkSectionsUnit_comp_fibreSections_app` — **the left-hand side of the
  composition clause, in normal form.**
* `AlgebraicGeometry.derivedGeometricStalkSections_app` and
  `AlgebraicGeometry.geometricFibreDerivedBaseChangeAb_app` — the two components of the right-hand
  side, written out.
* `AlgebraicGeometry.fibreSectionsRestrictionAb_eq` — restriction of global sections from the base
  change to the strict henselization down to the geometric fibre, written through the composition
  isomorphism the derived map to the fibre uses. This is the bridge from the normal form above to
  the underived core
  `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb`.

## Implementation notes

*Where the reduction stands.* The left-hand component is closed, and the right-hand component
expands: applying `CategoryTheory.Functor.rightDerived_ext` to the clause, then
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_fac_app` and
`stalkSectionsUnit_comp_fibreSections_app` on the left, and naturality of
`AlgebraicGeometry.derivedGeometricStalkToPullbackSections` at the unit of `Rf_*` followed by
`derivedGeometricStalkSections_app` and `geometricFibreDerivedBaseChangeAb_app` on the right,
leaves one equality of two explicit composites, both beginning with the identification
`(smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app (f_*J)` of the two actions of the
stalk. That equality is proved in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedStalkFibreComposition.lean`, by the
rearrangement described next. On the right-hand component the three identities the reduction needs
are now all available — `derivedGeometricStalkSections_app` and
`geometricFibreDerivedBaseChangeAb_app` below, together with
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac`,
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app`,
`Stacks.EtaleCohomology.mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso`
and its inverse form above — and what remains is the rearrangement that brings the right-hand
component to the same normal form, followed by one comparison of degreewise maps. Written out, the
right-hand component at `J` is

```
(Rf_*)_s-unit ≫ (derivedGeometricStalkToPullbackSections s.hom).app (Rf_*(Qh J)) ≫
  RΓ(s).map ((geometricFibreDerivedBaseChangeAb f s).app (Qh J)) ≫
  (smallEtaleDerivedGlobalSectionsPushforwardIsoAb q).hom.app (q⁻¹(Qh J))
```

and the rearrangement is: naturality of
`AlgebraicGeometry.derivedGeometricStalkToPullbackSections` at the unit of `Rf_*`, then
`derivedGeometricStalkSections_app`; then `geometricFibreDerivedBaseChangeAb_app`, naturality of
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage` at that
unit, `...mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso` and
`etaleAbelianDerivedBaseChange_fac`; then its inverse form on the fibre, naturality of the unit of
`RΓ(s, -)`, `smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app`, naturality of that
isomorphism and of the unit of `RΓ(X_s, -)`; and finally
`Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three`. The degreewise maps inside `Qh` are
then compared by `pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb`
together with `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange` and
`fibreSectionsRestrictionAb_eq`. That rearrangement is not carried out here, but nothing it needs
is missing any more: its first step — reading `etaleAbelianHomotopyBaseChange` at a complex as
the degreewise action of `etaleAbelianBaseChange`, which is what lets
`etaleAbelianDerivedBaseChange_fac` meet `mapHomotopyCategoryOfComp_comp_three` — is now
`Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange_app`, and the fourth device below records
the three shapes for it that the kernel rejects.

Assembling the mirror half directly reaches the conjugation of the base change transformation by
the two `NatTrans.mapHomotopyCategory` of the inverse-image identifications, and fails there with
`(kernel) deterministic timeout`: conjugating at the concrete functors instantiates the
comparison twice, once on each side, and each instantiation carries the whole
`smallEtalePullbackAbIsoEtaleAbelianInverseImage` bridge. The remedy is to state that
conjugation ONCE, generically in the transformation being conjugated — a
`mapHomotopyCategory_whisker_conj` taking the bridge as a hypothesis rather than inlining it —
so the expensive instantiation happens in a single place, and then to feed it
`etaleAbelianHomotopyBaseChange_app`. That is the same remedy as for the two sealed definitions:
pay the cost once, behind an interface, instead of at every use.

The generic conjugation, stated over abstract additive functors with the bridge as a hypothesis,
checks within the kernel's budget, whereas the concrete form exceeds it; it consists of four
lemmas (`map_three`, `id_sandwich`, a `_core` and the conjugation itself), which are not included
here because nothing consumes them yet. What remains after them is the last cost centre: the
concrete `etaleAbelianBaseChange` instantiation itself, which needs splitting into two steps so
that it too is instantiated once. The left half of the clause,
`stalkSectionsUnit_comp_fibreSections_app`, is already proved.

*Why the statements are so explicit, and why one isomorphism is a parameter.* Three devices are
used throughout, each forced by a failure of the more direct approach.

1. *A definition is unfolded once, at the level of natural transformations.* Computing the
   component of a transformation assembled from whiskerings and associators by definitional
   unfolding — `(derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J` against
   its four factors — exhausts the kernel's budget. Recording the definition itself as an equality
   of natural transformations (`stalkSectionsUnit_def`) is cheap, and the component is then
   computed from it by `simp only [NatTrans.comp_app, …]`.
2. *The rearrangements are stated for bare morphisms in an abstract category* and applied by
   `exact`, as in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/GeometricFibreBaseChangeSections.lean`: the composites
   involved are spelled through several definitionally equal but syntactically distinct
   descriptions of one object, so `rw` and `simp` cannot reassociate them in place, and
   `CategoryTheory.Category.comp_id` and `CategoryTheory.Functor.map_id` do not fire on them.
3. *The identification of the two iterated inverse images is a parameter, not
   `AlgebraicGeometry.geometricFibrePullbackAbCompIso`.* That definition is a composition
   isomorphism followed by an `eqToIso (congrArg …)` of
   `CategoryTheory.Limits.pullback.lift_fst`, and a definitional comparison which unfolds the
   transport does not terminate inside the kernel's budget: `lhsCompIso_app` and
   `lhsDegreewise_app` are stated for an arbitrary isomorphism `E` and instantiated at
   `geometricFibrePullbackAbCompIso` by plain substitution, which needs no such comparison. The
   body is sealed as well, so the comparison cannot be forced at all; the equations
   `AlgebraicGeometry.geometricFibrePullbackAbCompIso_hom` and its three companions
   (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkOfDerivedPushforward.lean`) are how the isomorphism is read, and
   `fibreSectionsRestrictionAb_eq` below rewrites with the first of them.
4. *`rw` leaves motives the kernel cannot check, even where it closes the goal.* The first device
   above says to record a definition as an equality of natural transformations rather than unfold
   it; the step the right-hand half needs first shows that the rest of that device — taking the
   component by `congrArg` and `CategoryTheory.NatTrans.comp_app`, never by `rw` — is just as
   necessary. That step is
   `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange_app`
   (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/BaseChangeMap.lean`), which is what lets
   `etaleAbelianDerivedBaseChange_fac` meet
   `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three`. Of the shapes for it,
   unfolding the definition inside a definitional comparison of components fails with
   `(kernel) deterministic timeout`; so does instantiating an abstract conjugation lemma at these
   functors; and so does `rw` with the definition followed by `NatTrans.comp_app`, which the
   elaborator accepts — it closes the goal — while the kernel cannot check the motives `rw` built
   over the whole composite. Binding the definition in a `have` at the level of natural
   transformations and taking the components by `congrArg` checks. The object identifications
   `((A ⋙ B).mapHomotopyCategory).obj K = (A.mapHomotopyCategory ⋙ B.mapHomotopyCategory).obj K`
   are *not* the obstruction: they are `rfl` in well under a second at these functors.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.DerivedFunctor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]
  {V : Type u₅} [Category.{v₅} V] [Abelian V]

/-- The comparison of homotopy categories attached to `e : F ⋙ G ≅ H` is, at an object of the
homotopy category, the quotient of the corresponding comparison of degreewise actions on
complexes. -/
public theorem mapHomotopyCategoryCompIso_hom_app (F : A₁ ⥤ A₂) (G : A₂ ⥤ A₃) (H : A₁ ⥤ A₃)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J =
      (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app J.as) :=
  rfl

/-- A functor carries a composite of three morphisms to the composite of their images. Stated for
bare morphisms, so that it applies by `exact` to a composite whose factors are spelled through
different but definitionally equal descriptions of one object. -/
private theorem map_comp_three {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D)
    {A B₁ B₂ B₃ : C} (a : A ⟶ B₁) (b : B₁ ⟶ B₂) (c : B₂ ⟶ B₃) {d : A ⟶ B₃}
    (h : a ≫ b ≫ c = d) :
    Fn.map a ≫ Fn.map b ≫ Fn.map c = Fn.map d := by
  rw [← Fn.map_comp, ← Fn.map_comp, h]

/-- A functor carries an equality between a composite of three morphisms and a composite of two
to the corresponding equality of composites of images. -/
private theorem map_comp_three_two {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D)
    {A B₁ B₂ B₃ B₄ : C} (a : A ⟶ B₁) (b : B₁ ⟶ B₂) (c : B₂ ⟶ B₃) {x : A ⟶ B₄} {y : B₄ ⟶ B₃}
    (h : a ≫ b ≫ c = x ≫ y) :
    Fn.map a ≫ Fn.map b ≫ Fn.map c = Fn.map x ≫ Fn.map y :=
  (map_comp_three Fn a b c h).trans (Fn.map_comp x y)

/-- Absorbing an identity and rewriting the last factor, in a composite of four. Stated for bare
morphisms so that it applies by `exact` to the component of a transformation assembled out of
whiskerings and associators, whose two middle factors are identities. -/
private theorem id_id_comp {C : Type*} [Category C] {A₀ A₁ A₂ : C} (α : A₀ ⟶ A₁) {i : A₁ ⟶ A₁}
    {E r : A₁ ⟶ A₂} (hi : i = 𝟙 A₁) (hE : E = r) : α ≫ 𝟙 A₁ ≫ i ≫ E = α ≫ r := by
  rw [hi, hE, Category.id_comp, Category.id_comp]

/-- Reading a factorization through an invertible comparison backwards: if `hm` cancels `iv` and
`iv ≫ x` is `r`, then `x` is `hm ≫ r`. -/
public theorem eq_comp_of_inv_comp {C : Type*} [Category C] {A₀ A₁ A₂ : C} {hm : A₀ ⟶ A₁}
    {iv : A₁ ⟶ A₀} {x : A₀ ⟶ A₂} {r : A₁ ⟶ A₂} (hid : hm ≫ iv = 𝟙 A₀) (h : iv ≫ x = r) :
    x = hm ≫ r := by
  rw [← h, ← Category.assoc, hid, Category.id_comp]

/-- Absorbing an identity in the middle of a composite of three. -/
private theorem id_middle {C : Type*} [Category C] {A₀ A₁ A₂ : C} (α : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) :
    α ≫ 𝟙 A₁ ≫ b = α ≫ b := by
  rw [Category.id_comp]

/-- **The rearrangement carrying the left-hand side of the composition clause of Stacks 0GIX to
its normal form.** Stated for bare morphisms in an abstract category, for the reason recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedFibreBaseChangeComposition.lean`: the
composites it rearranges are spelled through several definitionally equal but syntactically
distinct descriptions of one object, which stops `rw` from reassociating them in place. -/
private theorem lhs_rearrange {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ B₃ B₄ B₅ : C}
    (α : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (d : A₄ ⟶ A₅) (t : A₅ ⟶ A₆)
    {d' : A₃ ⟶ B₁} {g : B₁ ⟶ A₅} {a₂ : A₂ ⟶ B₂} {b₂ : B₂ ⟶ B₃} {c₂ : B₃ ⟶ B₁}
    {m : B₃ ⟶ B₄} {c' : B₄ ⟶ A₆} {n : B₂ ⟶ B₅} {b' : B₅ ⟶ B₄} {a' : A₁ ⟶ B₅}
    (h2 : c ≫ d = d' ≫ g) (h3 : b ≫ d' = a₂ ≫ b₂ ≫ c₂)
    (h4 : c₂ ≫ g ≫ t = m ≫ c') (h5 : b₂ ≫ m = n ≫ b') (h6 : a ≫ a₂ ≫ n = a') :
    (α ≫ a ≫ b ≫ c) ≫ d ≫ t = α ≫ a' ≫ b' ≫ c' := by
  simp only [Category.assoc]
  rw [reassoc_of% h2, reassoc_of% h3, h4, reassoc_of% h5, reassoc_of% h6]

/-- **A three-step degreewise composite, on homotopy categories.** For `β : St ⟶ R ⋙ Γ`,
`γ : P ⋙ R ⟶ N ⋙ Q` and an identification `δ : Q ⋙ Γ ≅ Γ'`, the degreewise action of `β` after
`P`, followed by that of `γ` inside `Γ` and by the comparison attached to `δ`, is the degreewise
action of the composite transformation `P ⋙ St ⟶ N ⋙ Γ'`. -/
public theorem mapHomotopyCategoryOfComp_comp_three
    (P : A₁ ⥤ A₂) [P.Additive] (St : A₂ ⥤ V) [St.Additive] (R : A₂ ⥤ A₃) [R.Additive]
    (Γ : A₃ ⥤ V) [Γ.Additive] (N : A₁ ⥤ A₄) [N.Additive] (Q : A₄ ⥤ A₃) [Q.Additive]
    (Γ' : A₄ ⥤ V) [Γ'.Additive]
    (β : St ⟶ R ⋙ Γ) (γ : P ⋙ R ⟶ N ⋙ Q) (δ : Q ⋙ Γ ≅ Γ')
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp St R Γ β).app
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((mapHomotopyCategoryOfComp (P ⋙ R) N Q γ).app J) ≫
        (Functor.mapHomotopyCategoryCompIso δ (ComplexShape.up ℤ)).hom.app
          ((N.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) =
      (mapHomotopyCategoryOfComp (P ⋙ St) N Γ'
        (Functor.whiskerLeft P β ≫ Functor.whiskerRight γ Γ ≫
          Functor.whiskerLeft N δ.hom)).app J := by
  rw [mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app,
    mapHomotopyCategoryOfComp_app, mapHomotopyCategoryCompIso_hom_app]
  exact map_comp_three (HomotopyCategory.quotient V (ComplexShape.up ℤ))
    ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.as))
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex γ (ComplexShape.up ℤ)).app J.as))
    ((Functor.mapHomologicalComplexCompIso δ (ComplexShape.up ℤ)).hom.app
      ((N.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.as))
    (HomologicalComplex.hom_ext _ _ fun i => rfl)

end Stacks.DerivedFunctor

namespace Stacks.DerivedCategoryComparisons

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F G : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)

/-- **The comparison of the degreewise actions of two isomorphic exact functors, read against the
inverses of both the factorizations through the homotopy category and the comparison itself.**
The inverse form of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso`, obtained
from it by cancelling the comparison. -/
public theorem mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso_inv
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app J ≫
        (mapDerivedCategoryIsoOfNatIso F G e).inv.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app J) ≫
        F.mapDerivedCategoryFactorsh.inv.app J := by
  have hid : DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app J) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app J) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id,
      NatTrans.id_app]
    exact CategoryTheory.Functor.map_id _ _
  refine Stacks.DerivedFunctor.eq_comp_of_inv_comp hid ?_
  rw [← Category.assoc, ← mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso F G e J,
    Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Stacks.DerivedCategoryComparisons

namespace Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The derived identification of the two inverse images of abelian étale sheaves, read on the
image of `DerivedCategory.Qh` and in the other direction.** The inverse form of
`Stacks.EtaleCohomology.mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso`,
which is the direction in which the derived base change map of Stacks 0A2A leaves the
etale-abelian vocabulary: that map is produced with
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImage` on the right, and it is the inverse of
the identification that carries it back to
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb`.

Nothing is assumed of the morphism. -/
public theorem mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso_inv
    {X Y : Scheme.{u}} (k : X ⟶ Y)
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    (etaleAbelianInverseImage.{u, u + 1} k).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage k).inv.app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
            (smallEtalePullbackAbIsoEtaleAbelianInverseImage k).inv (.up ℤ)).app J) ≫
        (smallEtalePullbackAb k).mapDerivedCategoryFactorsh.inv.app J :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso_inv
    _ _ (smallEtalePullbackAbIsoEtaleAbelianInverseImage k) J

end Stacks.EtaleCohomology

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits in
/-- Mathlib's composition isomorphism followed by the change of functor along `e` is the
project's composition isomorphism attached to `e`. -/
private theorem mapDerivedCategoryCompIso_hom_comp_mapDerivedCategory_hom
    {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    (mapDerivedCategoryCompIso F G).hom ≫ NatTrans.mapDerivedCategory e.hom =
      (mapDerivedCategoryCompIsoOfCompIso e).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) (fun K => ?_)
  rw [NatTrans.comp_app, mapDerivedCategoryCompIso_hom_app_Q_obj,
    NatTrans.mapDerivedCategory_app_Q_obj, mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp_assoc]
  congr 4
  ext n
  simp

/-- **The composition isomorphism on the image of `DerivedCategory.Qh`, with the two
factorizations of the composed actions cancelled.** This is
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh` read against the inverses of the
factorizations for `F` and for `G`, which is the shape a right derived descent out of a composite
of two exact functors presents: the descent arrives with those inverses in front of the
composition isomorphism, and cancelling them leaves only the degreewise comparison on homotopy
categories and the factorization for `H`. -/
public theorem mapDerivedCategoryFactorsh_inv_comp_mapDerivedCategoryCompIso_hom
    {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app J) ≫
        (mapDerivedCategoryCompIsoOfCompIso e).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) ≫
        H.mapDerivedCategoryFactorsh.inv.app J := by
  rw [mapDerivedCategoryCompIso_hom_app_Qh, ← Category.assoc
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app J)),
    ← G.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  have hid : G.mapDerivedCategory.map
      (𝟙 ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj J)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [hid, Category.id_comp, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- Restriction of sections from the base change to the strict henselization down to the
geometric fibre, written through the composition isomorphism
`AlgebraicGeometry.geometricFibrePullbackAbCompIso` that the derived map to the fibre uses. -/
public theorem fibreSectionsRestrictionAb_eq :
    smallEtaleSectionsRestrictionAb (strictHenselizationBaseChangeToSource B hS f s)
        (geometricFibreToStrictHenselizationBaseChange B hS f s) (geometricFibreToSource f s)
        (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s) =
      Functor.whiskerLeft (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleGlobalSectionsRestrictionAb
            (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
        Functor.whiskerRight (geometricFibrePullbackAbCompIso B hS f s).hom
          (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}) := by
  rw [geometricFibrePullbackAbCompIso_hom]
  rfl

/-- The comparison out of which the map from the stalk is descended, written out: this is its
definition, recorded at the level of natural transformations so that its components can be
computed without unfolding the definition again. -/
private theorem stalkSectionsUnit_def :
    derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s =
      Functor.whiskerLeft ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom ≫
        (Functor.associator ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          ((smallEtaleStalkAb s.hom).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)) (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f s) :=
  rfl

/-- The comparison on the homotopy category out of which the map from the stalk is descended,
at a complex: the identification of the two actions of the stalk, the degreewise map on sheaves,
and the unit of the derivation of global sections on the base change. -/
public theorem stalkSectionsUnit_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
            (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)).app J) ≫
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s)).app
              ((Functor.mapHomotopyCategory (smallEtalePullbackAb
                (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj J) ≫
            (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).map
              ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
                |>.mapDerivedCategoryFactorsh.inv.app J) := by
  rw [stalkSectionsUnit_def]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  refine Stacks.DerivedFunctor.id_id_comp _ ?_
    (Stacks.DerivedFunctor.exactDerivedDescUnit_app _ _ _ _ _ _ J)
  exact (congrArg DerivedCategory.Qh.map
      (Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_refl_hom_app _ _ J)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The map to the geometric fibre, written out at an object of the unbounded derived category:
the derived restriction of global sections along the canonical morphism from the fibre, followed
by the identification of the two iterated inverse images. -/
public theorem fibreSections_app (K : smallEtaleDerivedCategory X) :
    (strictHenselizationSectionsToFibreSections B hS f s).app K =
      (smallEtaleDerivedGlobalSectionsRestriction
            (geometricFibreToStrictHenselizationBaseChange B hS f s)).app
          ((smallEtaleDerivedPullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).obj K) ≫
        (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          ((Functor.mapDerivedCategoryCompIsoOfCompIso
            (geometricFibrePullbackAbCompIso B hS f s)).hom.app K) := by
  rw [← Functor.mapDerivedCategoryCompIso_hom_comp_mapDerivedCategory_hom]
  exact Stacks.DerivedFunctor.id_middle _ _

/-- The three composition isomorphisms in front of the identification of the two iterated inverse
images cancel, leaving the degreewise comparison and the identification for the composite. This is
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_inv_comp_mapDerivedCategoryCompIso_hom` read
inside derived global sections on the geometric fibre.

The identification `E` of the two iterated inverse images is a parameter rather than
`AlgebraicGeometry.geometricFibrePullbackAbCompIso` itself: that definition inlines an
`eqToIso (congrArg …)`, and a definitional comparison which unfolds it does not terminate inside
the kernel's budget. Keeping it abstract here means the instantiation is a plain substitution. -/
private theorem lhsCompIso_app
    (E : smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
      smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s) ≅
      smallEtalePullbackAb (geometricFibreToSource f s))
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          ((smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s)
            |>.mapDerivedCategoryFactorsh.inv.app
            ((Functor.mapHomotopyCategory (smallEtalePullbackAb
              (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj J))) ≫
        (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          ((smallEtaleDerivedPullbackAb
              (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
            ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)
              |>.mapDerivedCategoryFactorsh.inv.app J))) ≫
        (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          ((Functor.mapDerivedCategoryCompIsoOfCompIso E).hom.app (DerivedCategory.Qh.obj J)) =
      (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso E (.up ℤ)).hom.app J)) ≫
        (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
          ((smallEtalePullbackAb (geometricFibreToSource f s)
            |>.mapDerivedCategoryFactorsh.inv.app J)) :=
  Stacks.DerivedFunctor.map_comp_three_two _ _ _ _
    (CategoryTheory.Functor.mapDerivedCategoryFactorsh_inv_comp_mapDerivedCategoryCompIso_hom E J)

/-- The degreewise part of the left-hand side: the degreewise map from the stalk, the degreewise
restriction of sections to the fibre and the comparison of homotopy categories attached to the
identification `E` of the two iterated inverse images compose to the degreewise action of the
composite transformation. As in
`AlgebraicGeometry.lhsCompIso_app`, `E` is a parameter. -/
private theorem lhsDegreewise_app
    (E : smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
      smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s) ≅
      smallEtalePullbackAb (geometricFibreToSource f s))
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
            (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)).app J) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
            (smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s))
            (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1})
            (smallEtaleGlobalSectionsRestrictionAb
              (geometricFibreToStrictHenselizationBaseChange B hS f s))).app
          ((Functor.mapHomotopyCategory (smallEtalePullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategory
            (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}) (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso E (.up ℤ)).hom.app J)) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
        (smallEtalePullbackAb (geometricFibreToSource f s))
        (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1})
        (pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
          Functor.whiskerLeft
              (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
              (smallEtaleGlobalSectionsRestrictionAb
                (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
            (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight E.hom
              (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}))).app J) :=
  Stacks.DerivedFunctor.map_comp_three DerivedCategory.Qh _ _ _
    (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_trans _ _ _ _ _ _ _ _ E J)

/-- **The left-hand side of the composition clause of Stacks 0GIX, in normal form.** At a complex
`J`, the comparison out of which the map from the stalk is descended, followed by the map to the
geometric fibre, is the identification of the two actions of the stalk, the degreewise composite
of the map on sheaves with restriction of sections to the fibre, and the unit of the derivation of
global sections on the fibre. -/
public theorem stalkSectionsUnit_comp_fibreSections_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J ≫
        (strictHenselizationSectionsToFibreSections B hS f s).app (DerivedCategory.Qh.obj J) =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
            (smallEtalePullbackAb (geometricFibreToSource f s))
            (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1})
            (pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
              Functor.whiskerLeft
                  (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
                  (smallEtaleGlobalSectionsRestrictionAb
                    (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
                (Functor.associator _ _ _).inv ≫
                Functor.whiskerRight (geometricFibrePullbackAbCompIso B hS f s).hom
                  (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}))).app J) ≫
          (smallEtaleDerivedGlobalSectionsUnit (geometricFibre f s)).app
              ((Functor.mapHomotopyCategory
                (smallEtalePullbackAb (geometricFibreToSource f s)) (.up ℤ)).obj J) ≫
            (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
              ((smallEtalePullbackAb (geometricFibreToSource f s)
                |>.mapDerivedCategoryFactorsh.inv.app J)) := by
  refine Eq.trans (congrArg₂ (· ≫ ·) (stalkSectionsUnit_app B hS f s J)
    (fibreSections_app B hS f s (DerivedCategory.Qh.obj J))) ?_
  exact Stacks.DerivedFunctor.lhs_rearrange _ _ _ _ _ _
    ((smallEtaleDerivedGlobalSectionsRestriction
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).naturality
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)
          |>.mapDerivedCategoryFactorsh.inv.app J)))
    (smallEtaleDerivedGlobalSectionsRestriction_fac_app
      (geometricFibreToStrictHenselizationBaseChange B hS f s)
      ((Functor.mapHomotopyCategory
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)) (.up ℤ)).obj J))
    (lhsCompIso_app B hS f s (geometricFibrePullbackAbCompIso B hS f s) J)
    ((smallEtaleDerivedGlobalSectionsUnit (geometricFibre f s)).naturality
      ((Functor.mapHomotopyCategoryCompIso (geometricFibrePullbackAbCompIso B hS f s)
        (.up ℤ)).hom.app J)).symm
    (lhsDegreewise_app B hS f s (geometricFibrePullbackAbCompIso B hS f s) J)

/-! ### The right-hand side: the two components the reduction needs -/

/-- The derived comparison of the stalk with derived global sections on the geometric point, at
the image of a complex: the identification of the two actions of the stalk, the degreewise
comparison of Stacks 03Q1, and the unit of the derivation of global sections on the point.

This is `AlgebraicGeometry.derivedGeometricStalkToPullbackSections_fac_app` with the
identification of the two actions of the stalk cancelled, which is the side on which the
right-hand side of the composition clause presents it. -/
public theorem derivedGeometricStalkSections_app
    (M : HomotopyCategory (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ)) :
    (derivedGeometricStalkToPullbackSections s.hom).app (DerivedCategory.Qh.obj M) =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
            (smallEtaleStalkAb s.hom) (smallEtalePullbackAb s.hom)
            (Sheaf.Γ (smallEtaleTopology s.source) Ab.{u + 1})
            (geometricStalkToPullbackSectionsAb s.hom)).app M) ≫
          (smallEtaleDerivedGlobalSectionsUnit s.source).app
              ((Functor.mapHomotopyCategory (smallEtalePullbackAb s.hom) (.up ℤ)).obj M) ≫
            (smallEtaleDerivedGlobalSections s.source).map
              ((smallEtalePullbackAb s.hom).mapDerivedCategoryFactorsh.inv.app M) :=
  Stacks.DerivedFunctor.eq_comp_of_inv_comp (Iso.hom_inv_id_app _ _)
    (derivedGeometricStalkToPullbackSections_fac_app s.hom M)

/-- The derived base change map of the cartesian square defining the geometric fibre, written out
at an object of the unbounded derived category: this is its definition, recorded at the level of
natural transformations. -/
private theorem geometricFibreDerivedBaseChangeAb_def :
    geometricFibreDerivedBaseChangeAb f s =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage s.hom).hom ≫
        etaleAbelianDerivedBaseChange.{u, u + 1} f s.hom (geometricFibreToSource f s)
          (geometricFibreToPoint f s) pullback.condition ≫
        Functor.whiskerRight
          (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage
            (geometricFibreToSource f s)).inv
          (smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s)) :=
  rfl

/-- The derived base change map of the cartesian square defining the geometric fibre, at an
object: the identification of the two inverse images at the point, the derived base change map of
Stacks 0A2A, and the identification of the two inverse images on the fibre. -/
public theorem geometricFibreDerivedBaseChangeAb_app (K : smallEtaleDerivedCategory X) :
    (geometricFibreDerivedBaseChangeAb f s).app K =
      (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage s.hom).hom.app
          ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (etaleAbelianDerivedBaseChange.{u, u + 1} f s.hom (geometricFibreToSource f s)
          (geometricFibreToPoint f s) pullback.condition).app K ≫
        (smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s)).map
          ((smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage
            (geometricFibreToSource f s)).inv.app K) := by
  rw [geometricFibreDerivedBaseChangeAb_def]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rfl

end AlgebraicGeometry

end
