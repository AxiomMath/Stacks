module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.General.Approximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Extending functors from a full subcategory of schemes over a base

Let `S` be a scheme and let `𝒞` be a full subcategory of `Sch/S`, presented as the full
subcategory `P.FullSubcategory` cut out by an `ObjectProperty (Over S)`. Suppose `𝒞` contains,
up to isomorphism, every affine open of each of its objects (`HasAffineOpens`, condition (1) of
the source) and every affine scheme of finite presentation over an affine open of `S`
(`HasFinitePresentationAffines`, condition (2)). A set-valued functor on `𝒞` which is a Zariski
sheaf (`IsZariskiSheafOnSubcategory`, condition (a)) and takes directed inverse limits of affine
objects to filtered colimits (`PreservesAffineLimitsOnSubcategory`, condition (b)) extends to
`Sch/S` in a unique way.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.HasAffineOpens`,
  `AlgebraicGeometry.ExtendingFunctors.HasFinitePresentationAffines`: conditions (1) and (2)
  of the source on the full subcategory.
* `AlgebraicGeometry.ExtendingFunctors.IsZariskiSheafOnSubcategory`: condition (a), in the
  reading forced by the footnote of the source — the pairwise fibre products of a Zariski
  covering by objects of `𝒞` need not lie in `𝒞`, so compatibility of a family of sections is
  tested on a Zariski covering of each fibre product by objects of `𝒞`.
* `AlgebraicGeometry.ExtendingFunctors.IsZariskiSheaf`: the Zariski sheaf condition for a
  functor on all of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimitsOnSubcategory`,
  `AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits`: condition (b) on `𝒞` and on
  `Sch/S`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.extension_hom_unique`: a morphism between two extensions
  satisfying the analogues of (a) and (b) is determined by its restriction to `𝒞`.
* `AlgebraicGeometry.ExtendingFunctors.extension_iso_unique`: consequently two such extensions
  admit at most one isomorphism compatible with their identifications with the original functor.
* `AlgebraicGeometry.ExtendingFunctors.hom_ext_of_app_eq_on_subcategory`: the sharp form of the
  first statement, which needs only condition (2), the sheaf condition on the target and the
  limit condition on the source.
* `AlgebraicGeometry.ExtendingFunctors.exists_limit_of_isAffine_over_affineOpen`: an affine
  object of `Sch/S` whose structure morphism factors through an affine open of `S` is a directed
  inverse limit of objects of `Sch/S` each isomorphic to an object of `𝒞`.

## Implementation notes

Coverings are indexed by types in the universe `u` of the schemes, which is where the opens of a
scheme live; the covering of a scheme by the affine opens lying over affine opens of `S`, which
drives the proof, is indexed by the points of the scheme.

Condition (b) quantifies over inverse systems indexed by the opposite of a nonempty directed
poset, matching the source's "directed limit"; this is exactly the shape produced by the
presentation of an algebra as a filtered colimit of finitely presented algebras, which is how the
approximating systems are built.

The footnote's reading of condition (a) is recorded without reference to fibre products: a family
of open immersions `a i j k : U i j k ⟶ Y i` whose ranges cover `f i ⁻¹ (range (f j))` and which
satisfies `a i j k ≫ f i = b i j k ≫ f j` is precisely a Zariski covering of `Y i ×_X Y j` by
objects of `𝒞`, because `f j` is a monomorphism and a morphism whose composite with an open
immersion is an open immersion is itself one.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-! ### Open subobjects of an object of `Sch/S` -/

/-- The object of `Sch/S` attached to an open subscheme of `X`. -/
@[implicit_reducible]
def overOpen (X : Over S) (V : X.left.Opens) : Over S := Over.mk (V.ι ≫ X.hom)

/-- The underlying scheme of `overOpen X V` is the open subscheme `V`. -/
@[simp]
lemma overOpen_left (X : Over S) (V : X.left.Opens) : (overOpen X V).left = V.toScheme := rfl

/-- The structure morphism of `overOpen X V` is the inclusion of `V` followed by that of `X`. -/
@[simp]
lemma overOpen_hom (X : Over S) (V : X.left.Opens) : (overOpen X V).hom = V.ι ≫ X.hom := rfl

/-- The open immersion of an open subscheme of `X` into `X`, as a morphism of `Sch/S`. -/
@[implicit_reducible]
def overOpenι (X : Over S) (V : X.left.Opens) : overOpen X V ⟶ X := Over.homMk V.ι

/-- The underlying morphism of schemes of `overOpenι X V` is the open immersion `V.ι`. -/
@[simp]
lemma overOpenι_left (X : Over S) (V : X.left.Opens) : (overOpenι X V).left = V.ι := rfl

/-- The inclusion of open subobjects of `X` attached to an inclusion `V ≤ W` of opens. -/
@[implicit_reducible]
noncomputable def overOpenLE (X : Over S) {V W : X.left.Opens} (h : V ≤ W) :
    overOpen X V ⟶ overOpen X W :=
  Over.homMk (X.left.homOfLE h)

/-- The underlying morphism of schemes of `overOpenLE X h` is `X.left.homOfLE h`. -/
@[simp]
lemma overOpenLE_left (X : Over S) {V W : X.left.Opens} (h : V ≤ W) :
    (overOpenLE X h).left = X.left.homOfLE h := rfl

/-- The inclusion `overOpenLE X h` followed by the immersion of `W` is the immersion of `V`. -/
@[simp]
lemma overOpenLE_comp_overOpenι (X : Over S) {V W : X.left.Opens} (h : V ≤ W) :
    overOpenLE X h ≫ overOpenι X W = overOpenι X V := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, overOpenLE_left, overOpenι_left, overOpenι_left, Scheme.homOfLE_ι]

/-- Application of an equality of maps of types to an element. -/
private lemma hom_apply_eq {A B : Type w} {f g : A ⟶ B} (h : f = g) (a : A) : f a = g a := by
  rw [h]

/-! ### The conditions of the source -/

/-- **Condition (1) of Stacks 0EUW.** Every affine open of an object of the full subcategory is,
as a scheme over `S`, isomorphic to an object of the full subcategory. -/
def HasAffineOpens (P : ObjectProperty (Over S)) : Prop :=
  ∀ (X : Over S), P X → ∀ V : X.left.affineOpens,
    ∃ Y : Over S, P Y ∧ Nonempty (overOpen X V.1 ≅ Y)

/-- **Condition (2) of Stacks 0EUW.** Every affine scheme of finite presentation over an affine
open of `S` is, as a scheme over `S`, isomorphic to an object of the full subcategory. -/
def HasFinitePresentationAffines (P : ObjectProperty (Over S)) : Prop :=
  ∀ (U : S.affineOpens) (V : Scheme.{u}) (g : V ⟶ U.1.toScheme), IsAffine V →
    FinitePresentation g → ∃ Y : Over S, P Y ∧ Nonempty (Over.mk (g ≫ U.1.ι) ≅ Y)

/-- **Condition (a) of Stacks 0EUW**, in the reading forced by the footnote of the source.

For a Zariski covering `{f i : Y i ⟶ X}` of an object of the full subcategory by objects of the
full subcategory, the fibre products `Y i ×_X Y j` need not belong to the subcategory. A family
of open immersions `a i j k : U i j k ⟶ Y i` out of objects of the subcategory whose ranges cover
`f i ⁻¹ (range (f j))`, together with morphisms `b i j k : U i j k ⟶ Y j` satisfying
`a i j k ≫ f i = b i j k ≫ f j`, is exactly a Zariski covering of `Y i ×_X Y j` by objects of
the subcategory. The condition is that `F X` is the equalizer of the two maps
`∏ F (Y i) ⟶ ∏ F (U i j k)`. -/
def IsZariskiSheafOnSubcategory (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type w) : Prop :=
  ∀ (X : P.FullSubcategory) (ι : Type u) (Y : ι → P.FullSubcategory) (f : ∀ i, Y i ⟶ X)
    (_ : ∀ i, IsOpenImmersion (P.ι.map (f i)).left)
    (_ : ⨆ i, (P.ι.map (f i)).left.opensRange = ⊤)
    (K : ι → ι → Type u) (U : ∀ i j, K i j → P.FullSubcategory)
    (a : ∀ i j k, U i j k ⟶ Y i) (b : ∀ i j k, U i j k ⟶ Y j)
    (_ : ∀ i j k, IsOpenImmersion (P.ι.map (a i j k)).left)
    (_ : ∀ i j k, a i j k ≫ f i = b i j k ≫ f j)
    (_ : ∀ i j, ⨆ k, (P.ι.map (a i j k)).left.opensRange
      = (P.ι.map (f i)).left ⁻¹ᵁ (P.ι.map (f j)).left.opensRange)
    (s : ∀ i, F.obj (op (Y i))),
    (∀ i j k, F.map (a i j k).op (s i) = F.map (b i j k).op (s j)) →
      ∃! t : F.obj (op X), ∀ i, F.map (f i).op t = s i

/-- The Zariski sheaf condition for a functor on all of `Sch/S`: the sections over `X` are the
families of sections over the members of an open covering of `X` which agree on the pairwise
intersections. -/
def IsZariskiSheaf (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (X : Over S) (ι : Type u) (V : ι → X.left.Opens) (_ : ⨆ i, V i = ⊤)
    (s : ∀ i, F.obj (op (overOpen X (V i)))),
    (∀ i j, F.map (overOpenLE X (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
      = F.map (overOpenLE X (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)) →
      ∃! t : F.obj (op X), ∀ i, F.map (overOpenι X (V i)).op t = s i

/-- **Condition (b) of Stacks 0EUW.** A directed inverse limit of affine objects of the full
subcategory whose limit again lies in the full subcategory is carried to a filtered colimit. -/
def PreservesAffineLimitsOnSubcategory (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type w) : Prop :=
  ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (D : Λᵒᵖ ⥤ P.FullSubcategory) (_ : ∀ l, IsAffine (D.obj l).obj.left)
    (c : Cone D) (_ : IsLimit (P.ι.mapCone c)), Nonempty (IsColimit (F.mapCocone c.op))

/-- The analogue of condition (b) of Stacks 0EUW for a functor on all of `Sch/S`: a directed
inverse limit of affine schemes over `S` is carried to a filtered colimit. -/
def PreservesAffineLimits (F : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (D : Λᵒᵖ ⥤ Over S) (_ : ∀ l, IsAffine (D.obj l).left)
    (c : Cone D) (_ : IsLimit c), Nonempty (IsColimit (F.mapCocone c.op))

/-! ### Approximation by objects of the full subcategory -/

/-- An affine object of `Sch/S` whose structure morphism factors through an affine open of `S` is
the limit of an inverse system, indexed by the opposite of a nonempty directed poset, of
affine objects of `Sch/S`; if the full subcategory satisfies condition (2), every member of the
system is isomorphic to an object of the full subcategory. -/
theorem exists_limit_of_isAffine_over_affineOpen {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) (X : Over S) [IsAffine X.left] (U : S.affineOpens)
    (g : X.left ⟶ U.1.toScheme) (hg : g ≫ U.1.ι = X.hom) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ Over S) (c : Cone D) (_ : IsLimit c) (_ : c.pt ≅ X),
      (∀ l, IsAffine (D.obj l).left) ∧
        ∀ l, ∃ Y : Over S, P Y ∧ Nonempty (D.obj l ≅ Y) := by
  have hUaff : IsAffine U.1.toScheme := U.2
  obtain ⟨Λ, _, _, _, D₀, c₀, hc₀, e, b, hDaff, hbfp, hfac⟩ :=
    Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_directedOrder_affine_limit_presentation g
  let t : D₀ ⟶ (Functor.const Λᵒᵖ).obj S :=
    { app l := b.app l ≫ U.1.ι
      naturality := by
        intro l m h
        have hb := b.naturality h
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hb ⊢
        rw [← Category.assoc, hb] }
  let p : c₀.pt ⟶ S := e.inv ≫ X.hom
  have hp : ∀ l, c₀.π.app l ≫ t.app l = p := by
    intro l
    have h1 : e.inv ≫ g = c₀.π.app l ≫ b.app l := by
      rw [hfac l, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    change c₀.π.app l ≫ b.app l ≫ U.1.ι = e.inv ≫ X.hom
    rw [← Category.assoc, ← h1, Category.assoc, hg]
  refine ⟨Λ, inferInstance, inferInstance, inferInstance, Over.lift D₀ t,
    Over.liftCone D₀ t c₀ p hp, Over.isLimitLiftCone D₀ t c₀ p hp hc₀,
    Over.isoMk e.symm rfl, hDaff, fun l => ?_⟩
  have : IsAffine (D₀.obj l) := hDaff l
  let gl : D₀.obj l ⟶ U.1.toScheme := b.app l
  have : IsAffineHom gl := isAffineHom_of_isAffine gl
  exact hP U (D₀.obj l) gl (hDaff l) ⟨hbfp l, inferInstance, inferInstance⟩

/-! ### Uniqueness of the extension -/

/-- Two natural transformations agreeing at an object agree at every isomorphic object. -/
theorem app_eq_of_iso {C : Type*} [Category C] {D : Type*} [Category D] {F G : Cᵒᵖ ⥤ D}
    (θ θ' : F ⟶ G) {A B : C} (i : A ≅ B) (h : θ.app (op A) = θ'.app (op A)) :
    θ.app (op B) = θ'.app (op B) := by
  rw [← cancel_epi (F.map i.inv.op), θ.naturality i.inv.op, θ'.naturality i.inv.op, h]

/-- Two natural transformations of set-valued functors agreeing on a diagram whose image is a
colimit agree at the apex of the diagram. -/
theorem app_eq_of_isColimit {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type w} (θ θ' : F ⟶ G)
    {J : Type*} [Category J] {D : J ⥤ Cᵒᵖ} {t : Cocone D} (ht : IsColimit (F.mapCocone t))
    (h : ∀ j, θ.app (D.obj j) = θ'.app (D.obj j)) :
    θ.app t.pt = θ'.app t.pt :=
  ht.hom_ext fun j => by rw [Functor.mapCocone_ι_app, θ.naturality, θ'.naturality, h]

/-- Two natural transformations out of a functor satisfying the analogue of condition (b) which
agree on the objects of the full subcategory agree at every affine object of `Sch/S` whose
structure morphism factors through an affine open of `S`. -/
theorem app_eq_of_isAffine_over_affineOpen {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) {F G : (Over S)ᵒᵖ ⥤ Type w}
    (hbF : PreservesAffineLimits F) {θ θ' : F ⟶ G}
    (hagree : ∀ Y : Over S, P Y → θ.app (op Y) = θ'.app (op Y))
    (X : Over S) [IsAffine X.left] (U : S.affineOpens)
    (g : X.left ⟶ U.1.toScheme) (hg : g ≫ U.1.ι = X.hom) :
    θ.app (op X) = θ'.app (op X) := by
  obtain ⟨Λ, _, _, _, D, c, hc, ci, hDaff, hDmem⟩ :=
    exists_limit_of_isAffine_over_affineOpen hP X U g hg
  obtain ⟨hcol⟩ := hbF Λ D hDaff c hc
  refine app_eq_of_iso θ θ' ci (app_eq_of_isColimit θ θ' hcol fun l => ?_)
  obtain ⟨Y, hY, ⟨i⟩⟩ := hDmem l.unop
  exact app_eq_of_iso θ θ' i.symm (hagree Y hY)

/-- **The sharp form of the uniqueness in Stacks 0EUW.** Let `F` be a functor on `Sch/S` taking
directed inverse limits of affine schemes to filtered colimits and let `G` be a Zariski sheaf on
`Sch/S`. If the full subcategory contains, up to isomorphism, the affine schemes of finite
presentation over the affine opens of `S`, then two natural transformations `F ⟶ G` agreeing on
the objects of the full subcategory are equal. -/
theorem hom_ext_of_app_eq_on_subcategory {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) {F G : (Over S)ᵒᵖ ⥤ Type w}
    (hbF : PreservesAffineLimits F) (haG : IsZariskiSheaf G) (θ θ' : F ⟶ G)
    (hagree : ∀ Y : Over S, P Y → θ.app (op Y) = θ'.app (op Y)) :
    θ = θ' := by
  classical
  have key : ∀ X : Over S, θ.app (op X) = θ'.app (op X) := by
    intro X
    choose U₀ V₀ hxV gV hgV using fun x : X.left =>
      Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_affine_neighborhood_lift X.hom x
    have hcov : ⨆ x, (V₀ x).1 = ⊤ :=
      eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxV y⟩
    have hopen : ∀ x : X.left, θ.app (op (overOpen X (V₀ x).1))
        = θ'.app (op (overOpen X (V₀ x).1)) := by
      intro x
      have : IsAffine (overOpen X (V₀ x).1).left := (V₀ x).2
      exact app_eq_of_isAffine_over_affineOpen hP hbF hagree _ (U₀ x) (gV x) (hgV x)
    ext u
    have hcompat : ∀ x y : X.left,
        G.map (overOpenLE X (inf_le_left : (V₀ x).1 ⊓ (V₀ y).1 ≤ (V₀ x).1)).op
            (G.map (overOpenι X (V₀ x).1).op (θ.app (op X) u))
          = G.map (overOpenLE X (inf_le_right : (V₀ x).1 ⊓ (V₀ y).1 ≤ (V₀ y).1)).op
            (G.map (overOpenι X (V₀ y).1).op (θ.app (op X) u)) := by
      intro x y
      simp only [← Functor.map_comp_apply, ← op_comp, overOpenLE_comp_overOpenι]
    obtain ⟨w, -, huniq⟩ := haG X X.left (fun x => (V₀ x).1) hcov
      (fun x => G.map (overOpenι X (V₀ x).1).op (θ.app (op X) u)) hcompat
    refine (huniq (θ.app (op X) u) fun x => rfl).trans
      ((huniq (θ'.app (op X) u) fun x => ?_)).symm
    have hnat : θ'.app (op X) ≫ G.map (overOpenι X (V₀ x).1).op
        = θ.app (op X) ≫ G.map (overOpenι X (V₀ x).1).op := by
      rw [← θ.naturality, ← θ'.naturality, hopen x]
    simpa using hom_apply_eq hnat u
  exact NatTrans.ext (funext fun Z => key Z.unop)

/-- **Stacks 0EUW.** The extension of `F` to `Sch/S` is unique: a morphism between two extensions
of `F` which both satisfy the analogues of (a) and (b) is determined by its restriction to the
full subcategory. -/
@[stacks 0EUW "uniqueness: a morphism between two extensions satisfying the analogues of (a) and
(b) is determined by the identifications of their restrictions with the original functor"]
theorem extension_hom_unique {P : ObjectProperty (Over S)}
    (_hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (_haF : IsZariskiSheafOnSubcategory P F)
    (_hbF : PreservesAffineLimitsOnSubcategory P F)
    {F₁ F₂ : (Over S)ᵒᵖ ⥤ Type w}
    (_ha₁ : IsZariskiSheaf F₁) (hb₁ : PreservesAffineLimits F₁)
    (ha₂ : IsZariskiSheaf F₂) (_hb₂ : PreservesAffineLimits F₂)
    {α : P.ι.op ⋙ F₁ ≅ F} {β : P.ι.op ⋙ F₂ ≅ F} (θ θ' : F₁ ⟶ F₂)
    (hθ : Functor.whiskerLeft P.ι.op θ ≫ β.hom = α.hom)
    (hθ' : Functor.whiskerLeft P.ι.op θ' ≫ β.hom = α.hom) :
    θ = θ' := by
  have hw : Functor.whiskerLeft P.ι.op θ = Functor.whiskerLeft P.ι.op θ' := by
    rw [← cancel_mono β.hom, hθ, hθ']
  exact hom_ext_of_app_eq_on_subcategory hP2 hb₁ ha₂ θ θ' fun Y hY =>
    NatTrans.congr_app hw (op ⟨Y, hY⟩)

/-- **Stacks 0EUW.** The extension of `F` to `Sch/S` is unique: two extensions of `F` which both
satisfy the analogues of (a) and (b) admit at most one isomorphism compatible with the
identifications of their restrictions with `F`. -/
@[stacks 0EUW "uniqueness: two extensions satisfying the analogues of (a) and (b) admit at most
one isomorphism compatible with the identifications of their restrictions with the original
functor"]
theorem extension_iso_unique {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F)
    {F₁ F₂ : (Over S)ᵒᵖ ⥤ Type w}
    (ha₁ : IsZariskiSheaf F₁) (hb₁ : PreservesAffineLimits F₁)
    (ha₂ : IsZariskiSheaf F₂) (hb₂ : PreservesAffineLimits F₂)
    {α : P.ι.op ⋙ F₁ ≅ F} {β : P.ι.op ⋙ F₂ ≅ F} (ε ε' : F₁ ≅ F₂)
    (hε : Functor.whiskerLeft P.ι.op ε.hom ≫ β.hom = α.hom)
    (hε' : Functor.whiskerLeft P.ι.op ε'.hom ≫ β.hom = α.hom) :
    ε = ε' :=
  Iso.ext (extension_hom_unique hP1 hP2 haF hbF ha₁ hb₁ ha₂ hb₂ ε.hom ε'.hom hε hε')

end AlgebraicGeometry.ExtendingFunctors

end
