module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent data in terms of sheaves

Let `(C, J)` be a site, let `S : C` and let `{f i : X i ⟶ S}` be a covering of `S`. Stacks 02W5
identifies two categories: on one side the descent data for the covering whose components are
objects of the site, on the other the sheaves `G` on the slice site `C/S` for which every product
`h_{X i} ⨯ G` is representable. Moreover the object representing `h_{X i} ⨯ G` is the `i`-th
component of the corresponding descent datum, and `G` is representable exactly when that descent
datum is effective.

Both sides are read inside the category of sheaves. The ambient identification is Stacks 04TS,
`CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`: sheaves on
`C/S` are the same thing as glueing data for the covering, a sheaf on each `C/X i` together with
isomorphisms over the overlaps. Stacks 02W5 is that equivalence restricted to the objects whose
components are representable, and a descent datum of representable sheaves is, by the Yoneda
lemma, exactly a descent datum of objects of the site.

The translation between the two ways of saying that a sheaf is representable over one member of
the covering — that `h_{X i} ⨯ G` is representable, and that the restriction of `G` to `C/X i` is
representable — is Stacks 02W6, proved here as
`CategoryTheory.isRepresentable_overMap_iff` in the generality of an arbitrary presheaf of types
on a slice category.

## Main definitions

* `CategoryTheory.GrothendieckTopology.locallyRepresentable`: the sheaves on `C/S` whose
  restriction to each `C/X i` is representable, equivalently (by Stacks 02W6) those for which
  every `h_{X i} ⨯ G` is representable.
* `CategoryTheory.GrothendieckTopology.descentDataRepresentable`: the descent data for the
  covering whose components are representable sheaves.
* `CategoryTheory.GrothendieckTopology.effectiveDescentData`: the effective descent data, those
  isomorphic to the canonical descent datum of an object of the site over `S`.
* `CategoryTheory.Functor.RepresentableBy.prodYoneda` and
  `CategoryTheory.Functor.RepresentableBy.overForget`: the two halves of the comparison between a
  representation of `h_a ⨯ F` and a representation of the restriction of `F` to `C/a`.
* `CategoryTheory.Functor.RepresentableBy.overMapYoneda`: the restriction of a representable
  presheaf on `C/a` along `Over.map g` is represented by the fibre product.
* `CategoryTheory.GrothendieckTopology.sheafHomEquivOfRepresentableBy`: a morphism of
  representable sheaves is a morphism of the objects representing them.

## Main results

* `CategoryTheory.GrothendieckTopology.locallyRepresentableEquivalence` is Stacks 02W5: the
  sheaves on `C/S` which are representable over every member of the covering are equivalent to
  the descent data for the covering with representable components.
* `CategoryTheory.GrothendieckTopology.representableByProdYoneda` is part (1): the object
  representing `h_{X i} ⨯ G` is the object over `X i` representing the `i`-th component of the
  descent datum of `G`, viewed over `S`.
* `CategoryTheory.GrothendieckTopology.effectiveDescentData_toDescentData_iff` is part (2): the
  descent datum of `G` is effective if and only if `G` is representable.
* `CategoryTheory.isRepresentable_overMap_iff` is Stacks 02W6, and
  `CategoryTheory.isRepresentable_overForget_iff` is its absolute form.
* `CategoryTheory.isRepresentable_whiskerLeft_op_iff`: representability of a presheaf of types is
  invariant under restriction along an equivalence of categories.

## Implementation notes

The source's two sides are a category of descent data of *schemes* and a category of *sheaves*.
Here both are categories of sheaves, the first being the full subcategory
`descentDataRepresentable` of `CategoryTheory.Pseudofunctor.DescentData` for the pseudofunctor
`J.pseudofunctorOver (Type v)` cut out by representability of the components. By the Yoneda lemma
this is the source's category, and the dictionary is spelled out in three statements. An object of
it is a family of representable sheaves on the `C/X i`, that is a family of objects over the
`X i` by `CategoryTheory.GrothendieckTopology.representableByProdYoneda`. Its transition
isomorphisms live over the overlaps, and the restriction to an overlap `Y` of the sheaf
represented by `Z ⟶ X i` is represented by the fibre product `Z ×_{X i} Y`
(`CategoryTheory.Functor.RepresentableBy.overMapYoneda`), so they are isomorphisms of objects of
the site — for `Y = X i ×_S X j` exactly the source's
`φ_{ij} : X_i ×_S X_j' ⟶ X_i' ×_S X_j`. Its morphisms are families of morphisms of the
representing objects commuting with those isomorphisms, by
`CategoryTheory.GrothendieckTopology.sheafHomEquivOfRepresentableBy`.

Recording the glueing at sheaf level rather than at object level is what removes the fibre
products `X i ×_S X j` from the statement; the source's indexing by those presupposes that they
exist, and the two agree whenever they do, by
`CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence`.

For the same reason effectivity is the essential image of
`(J.over S).yoneda ⋙ toDescentData f` rather than a condition on chosen fibre products: the
canonical descent datum of an object `Z ⟶ S` of the site has `i`-th component the restriction of
`h_Z` to `C/X i`, which is represented by `Z ×_S X i` when that fibre product exists but needs no
fibre product to be written down. Subcanonicality of `J` is the source's observation that
representable presheaves are sheaves on the site, which is what lets `h_Z` be named as a sheaf at
all; `(J.over S).Subcanonical` follows from `J.Subcanonical` by
`CategoryTheory.GrothendieckTopology.subcanonical_over`.

The hypothesis `HasLimitsOfSize.{max u v, max u v} (Type v)` is inherited from Stacks 04TS, where
the limits are what the glued sheaf is built from. It holds whenever the universe of the objects
of `C` is at most that of its morphisms, in particular for a small site.

The comparison of Stacks 02W6 is proved for an arbitrary presheaf of types on a slice category and
is independent of the topology. `CategoryTheory.isRepresentable_overForget_iff` compares a
presheaf `F` on a category `D` with its restriction along `CategoryTheory.Over.forget a`, and
`CategoryTheory.isRepresentable_overMap_iff` transports that along
`CategoryTheory.Over.iteratedSliceEquiv` to the restriction along `CategoryTheory.Over.map`, which
is the restriction appearing in the glueing data. The transport uses
`CategoryTheory.isRepresentable_whiskerLeft_op_iff`, which is representability transfer along an
arbitrary equivalence.

## References

* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 02W6](https://stacks.math.columbia.edu/tag/02W6)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe t w₁ w₂ v u u'

namespace CategoryTheory

/-! ### Representability and restriction along an equivalence -/

namespace Functor.RepresentableBy

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v} B]

/-- A representation of a presheaf of types transports to a representation of its restriction
along an equivalence of categories, the representing object being transported by the inverse
equivalence. -/
def whiskerEquivalence (e : A ≌ B) {G : Bᵒᵖ ⥤ Type v} {b : B} (r : G.RepresentableBy b) :
    (e.functor.op ⋙ G).RepresentableBy (e.inverse.obj b) where
  homEquiv {x} := (e.toAdjunction.homEquiv x b).symm.trans r.homEquiv
  homEquiv_comp {x x'} g u := by
    dsimp
    rw [Adjunction.homEquiv_naturality_left_symm, r.homEquiv_comp]

/-- A representation of the restriction of a presheaf of types along an equivalence of categories
transports to a representation of the presheaf itself, the representing object being transported
by the equivalence. -/
def whiskerEquivalenceSymm (e : A ≌ B) {G : Bᵒᵖ ⥤ Type v} {A₀ : A}
    (r : (e.functor.op ⋙ G).RepresentableBy A₀) : G.RepresentableBy (e.functor.obj A₀) :=
  (r.whiskerEquivalence e.symm).ofIso
    (Functor.isoWhiskerRight (NatIso.op e.counitIso).symm G)

end Functor.RepresentableBy

/-- Representability of a presheaf of types is invariant under restriction along an equivalence of
categories. -/
theorem isRepresentable_whiskerLeft_op_iff {A : Type u} [Category.{v} A] {B : Type u'}
    [Category.{v} B] (e : A ≌ B) (G : Bᵒᵖ ⥤ Type v) :
    (e.functor.op ⋙ G).IsRepresentable ↔ G.IsRepresentable := by
  constructor
  · rintro ⟨a, ⟨r⟩⟩
    exact (r.whiskerEquivalenceSymm e).isRepresentable
  · rintro ⟨b, ⟨r⟩⟩
    exact (r.whiskerEquivalence e).isRepresentable

/-! ### A presheaf times a representable, and the restriction to a slice -/

namespace Functor.RepresentableBy

variable {D : Type u} [Category.{v} D] {a : D} {F : Dᵒᵖ ⥤ Type v}

/-- A representation of the restriction of `F` to `D/a` by an object `p : Z ⟶ a` is a
representation of `h_a ⨯ F` by `Z`: a morphism `V ⟶ Z` is the same thing as a morphism `V ⟶ a`
together with a section of `F` over `V`, by composing with `p` and by restricting the
tautological section. -/
@[sga "3 I 1.6.1" "partial"]
def prodYoneda {Z : D} {p : Z ⟶ a}
    (r : ((Over.forget a).op ⋙ F).RepresentableBy (Over.mk p)) :
    (FunctorToTypes.prod (yoneda.obj a) F).RepresentableBy Z where
  homEquiv {V} :=
    { toFun u := (u ≫ p, F.map u.op (r.homEquiv (𝟙 (Over.mk p))))
      invFun x := ((r.homEquiv (X := Over.mk x.1)).symm x.2).left
      left_inv u := by
        have h : (r.homEquiv (X := Over.mk (u ≫ p))) (Over.homMk u rfl) =
            F.map u.op (r.homEquiv (𝟙 (Over.mk p))) := r.homEquiv_eq _
        simp only [← h, Equiv.symm_apply_apply]
        rfl
      right_inv x := by
        obtain ⟨q, t⟩ := x
        refine Prod.ext (Over.w ((r.homEquiv (X := Over.mk q)).symm t)) ?_
        have h := (r.homEquiv (X := Over.mk q)).apply_symm_apply t
        rw [r.homEquiv_eq] at h
        exact h }
  homEquiv_comp {V V'} g u := by
    refine Prod.ext ?_ ?_
    · change (g ≫ u) ≫ p = g ≫ u ≫ p
      simp
    · change F.map (g ≫ u).op _ = F.map g.op (F.map u.op _)
      simp

variable {Z : D} (r : (FunctorToTypes.prod (yoneda.obj a) F).RepresentableBy Z)

/-- A representation of `h_a ⨯ F` by `Z` sends a morphism `u : V ⟶ Z` to the pair consisting of
`u` composed with the structure morphism `Z ⟶ a` and the restriction along `u` of the
tautological section of `F` over `Z`. -/
lemma prod_homEquiv_eq {V : D} (u : V ⟶ Z) :
    r.homEquiv u = (u ≫ (r.homEquiv (𝟙 Z)).1, F.map u.op (r.homEquiv (𝟙 Z)).2) := by
  rw [r.homEquiv_eq u]; rfl

/-- The pair read off by `prod_homEquiv_eq` from the morphism corresponding to a pair `(q, t)` is
that pair again. -/
lemma prod_homEquiv_symm_spec {V : D} (q : V ⟶ a) (t : F.obj (op V)) :
    (r.homEquiv.symm (q, t) ≫ (r.homEquiv (𝟙 Z)).1,
      F.map (r.homEquiv.symm (q, t)).op (r.homEquiv (𝟙 Z)).2) = (q, t) :=
  (r.prod_homEquiv_eq (r.homEquiv.symm (q, t))).symm.trans
    (r.homEquiv.apply_symm_apply (q, t))

/-- The morphism corresponding to a pair `(q, t)` lies over `q`. -/
lemma prod_homEquiv_symm_comp {V : D} (q : V ⟶ a) (t : F.obj (op V)) :
    r.homEquiv.symm (q, t) ≫ (r.homEquiv (𝟙 Z)).1 = q :=
  (Prod.ext_iff.mp (r.prod_homEquiv_symm_spec q t)).1

/-- Restricting the tautological section of `F` over `Z` along the morphism corresponding to a
pair `(q, t)` gives back `t`. -/
lemma prod_map_homEquiv_symm {V : D} (q : V ⟶ a) (t : F.obj (op V)) :
    F.map (r.homEquiv.symm (q, t)).op (r.homEquiv (𝟙 Z)).2 = t :=
  (Prod.ext_iff.mp (r.prod_homEquiv_symm_spec q t)).2

/-- A representation of `h_a ⨯ F` by `Z` is a representation of the restriction of `F` to `D/a` by
the structure morphism `Z ⟶ a` read off from it: a morphism `W ⟶ Z` over `a` is the same thing as
a section of `F` over `W`. -/
def overForget : ((Over.forget a).op ⋙ F).RepresentableBy (Over.mk (r.homEquiv (𝟙 Z)).1) where
  homEquiv {W} :=
    { toFun g := F.map g.left.op (r.homEquiv (𝟙 Z)).2
      invFun t := Over.homMk (r.homEquiv.symm (W.hom, t))
        (r.prod_homEquiv_symm_comp W.hom t)
      left_inv g := by
        apply Over.OverMorphism.ext
        change r.homEquiv.symm (W.hom, F.map g.left.op (r.homEquiv (𝟙 Z)).2) = g.left
        refine r.homEquiv.symm_apply_eq.2 ?_
        rw [r.prod_homEquiv_eq g.left]
        exact Prod.ext (Over.w g).symm rfl
      right_inv t := r.prod_map_homEquiv_symm W.hom t }
  homEquiv_comp {W W'} g' g := by
    change F.map (g' ≫ g).left.op _ = F.map g'.left.op (F.map g.left.op _)
    simp

/-- A representation of the restriction of a presheaf `F` on `C/S` along `Over.map T.hom` by an
object `Z` over `T.left` is a representation of `h_T ⨯ F` by `Z` viewed over `S`. -/
@[sga "3 I 1.6.1" "partial"]
noncomputable def prodYonedaOfOverMap {C : Type u} [Category.{v} C] {S : C} (T : Over S)
    {F : (Over S)ᵒᵖ ⥤ Type v} {Z : Over T.left}
    (r : ((Over.map T.hom).op ⋙ F).RepresentableBy Z) :
    (FunctorToTypes.prod (yoneda.obj T) F).RepresentableBy ((Over.map T.hom).obj Z) :=
  prodYoneda (p := (Over.homMk Z.hom : Over.mk (Z.hom ≫ T.hom) ⟶ T))
    (whiskerEquivalenceSymm (Over.iteratedSliceEquiv T).symm (G := (Over.forget T).op ⋙ F) r)

/-- The restriction along `Over.map g` of the presheaf on `C/a` represented by an object
`Z ⟶ a` is represented by the fibre product `Z ×_a Y`, for `g : Y ⟶ a`. -/
noncomputable def overMapYoneda {C : Type u} [Category.{v} C] {a Y : C} (g : Y ⟶ a) (Z : Over a)
    [HasPullback Z.hom g] :
    ((Over.map g).op ⋙ yoneda.obj Z).RepresentableBy (Over.mk (pullback.snd Z.hom g)) where
  homEquiv {W} :=
    { toFun w := Over.homMk (w.left ≫ pullback.fst Z.hom g) (by
        have hw : w.left ≫ pullback.snd Z.hom g = W.hom := Over.w w
        rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
        rfl)
      invFun u := Over.homMk (pullback.lift u.left W.hom (Over.w u)) (pullback.lift_snd _ _ _)
      left_inv w := Over.OverMorphism.ext <|
        pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Over.w w).symm)
      right_inv u := Over.OverMorphism.ext (pullback.lift_fst _ _ _) }
  homEquiv_comp {W W'} g' w := by
    apply Over.OverMorphism.ext
    simp

end Functor.RepresentableBy

/-- The restriction of a presheaf of types `F` on `D` to the slice category `D/a` is
representable if and only if the product `h_a ⨯ F` is representable. -/
theorem isRepresentable_overForget_iff {D : Type u} [Category.{v} D] (a : D) (F : Dᵒᵖ ⥤ Type v) :
    ((Over.forget a).op ⋙ F).IsRepresentable ↔ (yoneda.obj a ⨯ F).IsRepresentable := by
  constructor
  · rintro ⟨W, ⟨rW⟩⟩
    obtain ⟨Z, p, rfl⟩ := Over.mk_surjective W
    have := rW.prodYoneda.isRepresentable
    exact isRepresentable_of_natIso _ (FunctorToTypes.binaryProductIso (yoneda.obj a) F).symm
  · intro h
    obtain ⟨Z, ⟨r⟩⟩ : (FunctorToTypes.prod (yoneda.obj a) F).IsRepresentable :=
      isRepresentable_of_natIso _ (FunctorToTypes.binaryProductIso (yoneda.obj a) F)
    exact r.overForget.isRepresentable

/-- Let `S` be an object of a category `C`, let `T` be an object over `S` and let `F` be a presheaf
of types on `C/S`. Then the product `h_T ⨯ F` is representable if and only if the restriction of
`F` to `C/T.left` is representable. -/
@[stacks 02W6]
theorem isRepresentable_overMap_iff {C : Type u} [Category.{v} C] {S : C} (T : Over S)
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    ((Over.map T.hom).op ⋙ F).IsRepresentable ↔ (yoneda.obj T ⨯ F).IsRepresentable := by
  rw [← isRepresentable_overForget_iff T F,
    ← isRepresentable_whiskerLeft_op_iff (Over.iteratedSliceEquiv T).symm
      ((Over.forget T).op ⋙ F), ← Over.iteratedSliceBackward_forget T]
  rfl

/-! ### Components of an isomorphism of descent data -/

namespace Pseudofunctor.DescentData

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁, w₂}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- An isomorphism of descent data is an isomorphism on each component. -/
@[simps]
def objIso {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by rw [← comp_hom, e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom, e.inv_hom_id, id_hom]

end Pseudofunctor.DescentData

/-! ### Locally representable sheaves and descent data -/

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The sheaves of types on the slice site `C/S` whose restriction to each slice site `C/X i` of
a family `{f i : X i ⟶ S}` is representable. By Stacks 02W6 these are exactly the sheaves `G`
for which every product `h_{X i} ⨯ G` is representable; see
`CategoryTheory.GrothendieckTopology.locallyRepresentable_iff`. -/
def locallyRepresentable : ObjectProperty (Sheaf (J.over S) (Type v)) :=
  fun G => ∀ i, ((J.overMapPullback (Type v) (f i)).obj G).obj.IsRepresentable

/-- A sheaf on `C/S` is representable over every member of the family `{f i : X i ⟶ S}` exactly
when every product `h_{X i} ⨯ G` is representable, which is the form the condition takes in
Stacks 02W5. -/
theorem locallyRepresentable_iff (G : Sheaf (J.over S) (Type v)) :
    locallyRepresentable J f G ↔
      ∀ i, (CategoryTheory.yoneda.obj (Over.mk (f i)) ⨯ G.obj).IsRepresentable :=
  forall_congr' fun i => isRepresentable_overMap_iff (Over.mk (f i)) G.obj

/-- By the Yoneda lemma, a morphism between two representable sheaves on a site is a morphism
between the objects representing them. -/
noncomputable def sheafHomEquivOfRepresentableBy {D : Type u} [Category.{v} D]
    (K : GrothendieckTopology D) {M N : Sheaf K (Type v)} {Z₁ Z₂ : D}
    (r₁ : M.obj.RepresentableBy Z₁) (r₂ : N.obj.RepresentableBy Z₂) :
    (Z₁ ⟶ Z₂) ≃ (M ⟶ N) :=
  (Yoneda.fullyFaithful (C := D)).homEquiv.trans
    ((r₁.toIso.homCongr r₂.toIso).trans
      (fullyFaithfulSheafToPresheaf K (Type v)).homEquiv.symm)

/-- The descent data for a family `{f i : X i ⟶ S}`, in sheaves of types on the slice sites,
whose components are representable. By the Yoneda lemma these are the descent data whose
components are objects of the site over the `X i`. -/
def descentDataRepresentable :
    ObjectProperty ((J.pseudofunctorOver (Type v)).DescentData f) :=
  fun D => ∀ i, (D.obj i).obj.IsRepresentable

/-- Having representable components is invariant under isomorphism of descent data. -/
instance : (descentDataRepresentable J f).IsClosedUnderIsomorphisms where
  of_iso {D₁ D₂} e h i := by
    obtain ⟨Y, ⟨r⟩⟩ := h i
    exact ⟨Y, ⟨r.ofIso ((sheafToPresheaf _ _).mapIso (Pseudofunctor.DescentData.objIso e i))⟩⟩

/-- The `i`-th component of the canonical descent datum of a sheaf on `C/S` is its restriction to
`C/X i`. -/
lemma toDescentData_obj_obj (G : Sheaf (J.over S) (Type v)) (i : ι) :
    (((J.pseudofunctorOver (Type v)).toDescentData f).obj G).obj i =
      (J.overMapPullback (Type v) (f i)).obj G :=
  rfl

/-- A sheaf on `C/S` is representable over every member of a family exactly when its canonical
descent datum has representable components. -/
lemma descentDataRepresentable_inverseImage :
    (descentDataRepresentable J f).inverseImage ((J.pseudofunctorOver (Type v)).toDescentData f)
      = locallyRepresentable J f :=
  rfl

/-- Let `(C, J)` be a site, let `{f i : X i ⟶ S}` be a covering of an object `S` of `C`, and let
`G` range over the sheaves of types on the slice site `C/S`. The sheaves for which every product
`h_{X i} ⨯ G` is representable are equivalent to the descent data for the covering with
representable components, via the functor sending a sheaf to its canonical descent datum. -/
@[stacks 02W5 "the equivalence of categories", sga "3 IV 4.6.8"]
noncomputable def locallyRepresentableEquivalence
    [HasLimitsOfSize.{max u v, max u v} (Type v)] (hf : Sieve.ofArrows X f ∈ J S) :
    (locallyRepresentable J f).FullSubcategory ≌
      (descentDataRepresentable J f).FullSubcategory :=
  have := isEquivalence_toDescentData_pseudofunctorOver J (Type v) f hf
  Equivalence.congrFullSubcategory
    ((J.pseudofunctorOver (Type v)).toDescentData f).asEquivalence
    (descentDataRepresentable_inverseImage J f)

/-- The object representing the product `h_{X i} ⨯ G` is the object over `X i` representing the
`i`-th component of the canonical descent datum of `G`, viewed as an object over `S`. -/
@[stacks 02W5 "part (1): the representing objects are the components of the descent datum"]
noncomputable def representableByProdYoneda (G : Sheaf (J.over S) (Type v)) (i : ι)
    {Z : Over (X i)}
    (r : ((((J.pseudofunctorOver (Type v)).toDescentData f).obj G).obj i).obj.RepresentableBy Z) :
    (CategoryTheory.yoneda.obj (Over.mk (f i)) ⨯ G.obj).RepresentableBy
      ((Over.map (f i)).obj Z) :=
  (Functor.RepresentableBy.prodYonedaOfOverMap (Over.mk (f i)) r).ofIso
    (FunctorToTypes.binaryProductIso _ _).symm

/-- The *effective* descent data for a family `{f i : X i ⟶ S}`: those isomorphic to the canonical
descent datum of an object of the site over `S`. The `i`-th component of the canonical descent
datum of `Z ⟶ S` is the restriction of `h_Z` to `C/X i`, which is represented by `Z ×_S X i`
whenever that fibre product exists. -/
def effectiveDescentData [J.Subcanonical] :
    ObjectProperty ((J.pseudofunctorOver (Type v)).DescentData f) :=
  ((J.over S).yoneda ⋙ (J.pseudofunctorOver (Type v)).toDescentData f).essImage

/-- The canonical descent datum of a sheaf `G` on `C/S` relative to a covering `{f i : X i ⟶ S}` is
effective if and only if `G` is representable. -/
@[stacks 02W5 "part (2): representable if and only if effective", sga "3 IV 4.6.8" "partial"]
theorem effectiveDescentData_toDescentData_iff [J.Subcanonical]
    [HasLimitsOfSize.{max u v, max u v} (Type v)] (hf : Sieve.ofArrows X f ∈ J S)
    (G : Sheaf (J.over S) (Type v)) :
    effectiveDescentData J f (((J.pseudofunctorOver (Type v)).toDescentData f).obj G) ↔
      G.obj.IsRepresentable := by
  have := isEquivalence_toDescentData_pseudofunctorOver J (Type v) f hf
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    exact Functor.IsRepresentable.mk'
      ((sheafToPresheaf (J.over S) (Type v)).mapIso
        (((J.pseudofunctorOver (Type v)).toDescentData f).preimageIso e))
  · rintro ⟨Z, ⟨r⟩⟩
    exact ⟨Z, ⟨((J.pseudofunctorOver (Type v)).toDescentData f).mapIso
      ((fullyFaithfulSheafToPresheaf (J.over S) (Type v)).preimageIso r.toIso)⟩⟩

end GrothendieckTopology

end CategoryTheory

end
