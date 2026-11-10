module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Representation of a reindexed 2-fibre product by a presheaf

Let `K : D ⥤ E` be a functor, let `c : E ⥤ C` be a projection to a base, let `pX : X ⥤ C` and
`pY : Y ⥤ C` be two more categories over the base and let `G : Y ⥤ X` be a 1-morphism over it.
A family `M : E ⥤ X` of objects of `X` indexed by `E` has a 2-fibre product with `Y` over `X`,
and so does its reindexing `L : D ⥤ X` along `K`, once `L` is identified with `K ⋙ M` by a
*vertical* isomorphism `α`. This file shows that a representation of the former 2-fibre product
by a presheaf `N` on `E` induces a representation of the latter by any presheaf `V` on `D`
identified with the restriction of `N` along `K`.

## Main definitions

* `AlgebraicGeometry.Stack.equivalenceOverOfVerticalPreimages`: a fully faithful 1-morphism of
  categories over a base admitting vertical preimages is an equivalence over the base.
* `AlgebraicGeometry.Stack.reindexedLiftObj` and `AlgebraicGeometry.Stack.reindexedLiftMap`: the
  reindexing comparison, sending an object (resp. a morphism) of the 2-fibre product formed along
  `L` to one of the 2-fibre product formed along `M`.
* `AlgebraicGeometry.Stack.reindexedSectionFunctor`: the 1-morphism from the 2-fibre product
  formed along `L` to the category of elements of `V` which names the section of `V` attached to
  each object.

## Main results

* `AlgebraicGeometry.Stack.reindexedSectionEquivalenceOver`: the 2-fibre product formed along
  `L` is represented by `V`.
* `AlgebraicGeometry.Stack.reindexedLift_hom_ext`: a morphism of the 2-fibre product formed along
  `L` is determined by its first component.
* `AlgebraicGeometry.Stack.reindexedLiftSection_surjective`: every section of `N` over an object
  in the image of `K` is named by an object of the 2-fibre product formed along `L`.
* `AlgebraicGeometry.Stack.isIso_twoFibreProductOver_hom`: a morphism of a 2-fibre product whose
  base morphism and two components are isomorphisms is an isomorphism.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

/-! ### Equivalences over a base from vertical preimages -/

/-- A fully faithful 1-morphism of categories over a base admitting vertical preimages is an
equivalence over that base. -/
noncomputable def equivalenceOverOfVerticalPreimages {C A A' : Type*} [Category C]
    [Category A] [Category A'] {p : A ⥤ C} {q : A' ⥤ C} (T : A ⥤ A') (hT : T ⋙ q = p)
    [T.Full] [T.Faithful] (h : Functor.HasVerticalPreimages p q T) :
    StacksRepresentableCFG.EquivalenceOver p q :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver hT
    (Functor.isEquivalenceOver_of_exists_vertical_iso hT h)

/-- Two morphisms of a category over a base which lie over one and the same morphism of the base
agree, when the category is equivalent over the base to the category of elements of a presheaf of
sets. -/
theorem hom_ext_of_equivalenceOver {C A : Type*} [Category C] [Category A] {p : A ⥤ C}
    {N : Cᵒᵖ ⥤ Type*}
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (N ⋙ typeToCat)).p)
    {a b : A} {T T' : C} (f : T ⟶ T') (g h : a ⟶ b) (hg : p.IsHomLift f g)
    (hh : p.IsHomLift f h) : g = h := by
  have hg' : (presheafOfCategories (N ⋙ typeToCat)).p.IsHomLift f (e.hom.functor.map g) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w f g
  have hh' : (presheafOfCategories (N ⋙ typeToCat)).p.IsHomLift f (e.hom.functor.map h) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w f h
  have hbase : (presheafOfCategories (N ⋙ typeToCat)).p.map (e.hom.functor.map g) =
      (presheafOfCategories (N ⋙ typeToCat)).p.map (e.hom.functor.map h) := by
    rw [IsHomLift.fac' _ f (e.hom.functor.map g), IsHomLift.fac' _ f (e.hom.functor.map h)]
  exact Functor.FullyFaithful.map_injective e.toEquivalence.fullyFaithfulFunctor
    (PresheafOfCategories.elements_hom_ext _ _ hbase)

/-! ### Representation of a reindexed 2-fibre product -/

section ReindexedRepresentation

variable {C D E X Y : Type*} [Category C] [Category D] [Category E] [Category X] [Category Y]
  {c : E ⥤ C} {pX : X ⥤ C} {pY : Y ⥤ C} {K : D ⥤ E} {L : D ⥤ X} {M : E ⥤ X} {G : Y ⥤ X}
  (α : L ≅ K ⋙ M) (hα : ∀ T, pX.IsHomLift (𝟙 (c.obj (K.obj T))) (α.hom.app T))

/-- An object of the 2-fibre product formed along `L` read as an object of the 2-fibre product
formed along `M = K^* L`: apply `K` to the first component and absorb the component of `α` into
the comparison isomorphism. -/
def reindexedLiftObj (P : TwoFibreProductOver (K ⋙ c) pY pX L G) :
    TwoFibreProductOver c pY pX M G where
  base := P.base
  x := K.obj P.x
  y := P.y
  hx := P.hx
  hy := P.hy
  iso := (α.app P.x).symm ≪≫ P.iso
  vertical := by
    have hv := P.vertical
    have ha : pX.IsHomLift (𝟙 P.base) (α.app P.x).hom := by
      change pX.IsHomLift (𝟙 P.base) (α.hom.app P.x)
      rw [← P.hx]
      exact hα P.x
    exact IsHomLift.comp_lift_id_right pX (𝟙 P.base) (α.app P.x).inv P.iso.hom

attribute [local implicit_reducible] reindexedLiftObj

/-- A morphism of the 2-fibre product formed along `L` read as a morphism of the 2-fibre product
formed along `M`, by `AlgebraicGeometry.Stack.reindexedLiftObj`. -/
def reindexedLiftMap {P Q : TwoFibreProductOver (K ⋙ c) pY pX L G} (f : P ⟶ Q) :
    reindexedLiftObj α hα P ⟶ reindexedLiftObj α hα Q where
  hbase := f.hbase
  a := K.map f.a
  b := f.b
  ha := by
    have ha := f.ha
    exact Functor.isHomLift_map_of_comp_eq (G := K) rfl f.hbase f.a
  hb := f.hb
  w := by
    change (K ⋙ M).map f.a ≫ (α.inv.app Q.x ≫ Q.iso.hom) =
      (α.inv.app P.x ≫ P.iso.hom) ≫ G.map f.b
    rw [← Category.assoc, α.inv.naturality f.a, Category.assoc, f.w, Category.assoc]

attribute [local implicit_reducible] reindexedLiftMap

/-- A morphism of the 2-fibre product formed along `L` with prescribed first component is the same
thing as a morphism of the 2-fibre product formed along `M` lying over the image of that
component under `K`. -/
theorem reindexedLift_hom_iff {P Q : TwoFibreProductOver (K ⋙ c) pY pX L G}
    (f : P.x ⟶ Q.x) :
    (∃ g : P ⟶ Q, g.a = f) ↔
      ∃ g : reindexedLiftObj α hα P ⟶ reindexedLiftObj α hα Q,
        (TwoFibreProductOver.fst c pY pX M G).IsHomLift (K.map f) g := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨reindexedLiftMap α hα g,
      IsHomLift.map (TwoFibreProductOver.fst c pY pX M G) (reindexedLiftMap α hα g)⟩
  · rintro ⟨g, hg⟩
    have he : g.a = K.map f := by
      have hh := IsHomLift.fac' (TwoFibreProductOver.fst c pY pX M G) (K.map f) g
      change g.a = eqToHom rfl ≫ K.map f ≫ eqToHom rfl at hh
      simpa using hh
    refine ⟨TwoFibreProductOver.Hom.mk' f g.b ?_ ?_, rfl⟩
    · have hb := g.hb
      rw [IsHomLift.fac' pY g.hbase g.b]
      change eqToHom P.hy.symm ≫ (eqToHom P.hy ≫ g.hbase ≫ eqToHom Q.hy.symm) ≫
        eqToHom Q.hy = eqToHom P.hx.symm ≫ c.map (K.map f) ≫ eqToHom Q.hx
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id] using g.hbase_eq.trans (by rw [he])
    · have hw := g.w
      change M.map g.a ≫ (α.inv.app Q.x ≫ Q.iso.hom) =
        (α.inv.app P.x ≫ P.iso.hom) ≫ G.map g.b at hw
      have hn : M.map (K.map f) ≫ α.inv.app Q.x = α.inv.app P.x ≫ L.map f := α.inv.naturality f
      rw [he, ← Category.assoc, hn, Category.assoc] at hw
      exact (cancel_epi (α.inv.app P.x)).mp (by simpa only [Category.assoc] using hw)

variable {N : Eᵒᵖ ⥤ Type u}
  (e : StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.fst c pY pX M G)
    (presheafOfCategories (N ⋙ typeToCat)).p)

/-- The section of `N` named by an object of the 2-fibre product formed along `L`, through the
reindexing `AlgebraicGeometry.Stack.reindexedLiftObj` and the given representation of the 2-fibre
product formed along `M`. -/
def reindexedLiftSection (P : TwoFibreProductOver (K ⋙ c) pY pX L G) {T : E}
    (h : K.obj P.x = T) : N.obj (op T) :=
  PresheafOfCategories.sectionOfObj e (reindexedLiftObj α hα P) h

include α hα e in
/-- A morphism of the 2-fibre product formed along `L` is determined by its first component. -/
theorem reindexedLift_hom_ext {P Q : TwoFibreProductOver (K ⋙ c) pY pX L G} (f g : P ⟶ Q)
    (h : f.a = g.a) : f = g := by
  have hh := hom_ext_of_equivalenceOver e (K.map f.a) (reindexedLiftMap α hα f)
    (reindexedLiftMap α hα g)
    (IsHomLift.map (TwoFibreProductOver.fst c pY pX M G) (reindexedLiftMap α hα f))
    (by
      rw [h]
      exact IsHomLift.map (TwoFibreProductOver.fst c pY pX M G) (reindexedLiftMap α hα g))
  exact TwoFibreProductOver.Hom.ext' h (congrArg (fun t => t.b) hh)

/-- Every section of `N` over an object in the image of `K` is named by an object of the 2-fibre
product formed along `L` sitting over that object. -/
theorem reindexedLiftSection_surjective (T : D) (s : N.obj (op (K.obj T))) :
    ∃ (P : TwoFibreProductOver (K ⋙ c) pY pX L G) (hP : P.x = T),
      reindexedLiftSection α hα e P (congrArg K.obj hP) = s := by
  obtain ⟨a, ha, hs⟩ := PresheafOfCategories.exists_sectionOfObj e s
  rcases a with ⟨base, x, y, hx, hy, iso, hv⟩
  change x = K.obj T at ha
  subst x
  let P : TwoFibreProductOver (K ⋙ c) pY pX L G :=
    { base := base
      x := T
      y := y
      hx := hx
      hy := hy
      iso := α.app T ≪≫ iso
      vertical := by
        have hat : pX.IsHomLift (𝟙 base) (α.app T).hom := by
          change pX.IsHomLift (𝟙 base) (α.hom.app T)
          rw [← hx]
          exact hα T
        exact IsHomLift.comp_lift_id_right pX (𝟙 base) (α.app T).hom iso.hom }
  refine ⟨P, rfl, ?_⟩
  have he : reindexedLiftObj α hα P =
      (⟨base, K.obj T, y, hx, hy, iso, hv⟩ : TwoFibreProductOver c pY pX M G) := by
    dsimp only [reindexedLiftObj, P]
    congr 1
    exact Iso.ext (by simp)
  simpa only [reindexedLiftSection, he] using hs

include α hα in
/-- A morphism of the 2-fibre product formed along `M` between two reindexed objects and lying
over the image under `K` of a morphism of their first components is the same thing as a
restriction relation between the sections of `N` they name. -/
theorem reindexedLiftSection_hom_iff
    {P Q : TwoFibreProductOver (K ⋙ c) pY pX L G} (f : P.x ⟶ Q.x) :
    (∃ g : reindexedLiftObj α hα P ⟶ reindexedLiftObj α hα Q,
        (TwoFibreProductOver.fst c pY pX M G).IsHomLift (K.map f) g) ↔
      reindexedLiftSection α hα e P rfl =
        N.map (K.map f).op (reindexedLiftSection α hα e Q rfl) :=
  ⟨fun ⟨g, hg⟩ ↦ PresheafOfCategories.sectionOfObj_map e (W := K.obj Q.x) (W' := K.obj P.x) rfl
    rfl (K.map f) g hg,
    PresheafOfCategories.exists_hom_of_sectionOfObj_map e (W := K.obj Q.x) (W' := K.obj P.x) rfl
      rfl (K.map f)⟩

variable (V : Dᵒᵖ ⥤ Type u) (β : ∀ T, V.obj (op T) ≃ N.obj (op (K.obj T)))
  (hβ : ∀ {T T'} (f : T ⟶ T') (s : V.obj (op T')),
    β T (V.map f.op s) = N.map (K.map f).op (β T' s))

/-- The section of `V` named by an object of the 2-fibre product formed along `L`: the section of
`N` it names, read through the given identification of `V` with the restriction of `N` along
`K`. -/
def reindexedSectionValue (P : TwoFibreProductOver (K ⋙ c) pY pX L G) : V.obj (op P.x) :=
  (β P.x).symm (reindexedLiftSection α hα e P rfl)

include hβ in
/-- A morphism of the 2-fibre product formed along `L` with prescribed first component is the same
thing as a restriction relation between the sections of `V` named by its source and target. -/
theorem reindexedSectionValue_hom_iff
    {P Q : TwoFibreProductOver (K ⋙ c) pY pX L G} (f : P.x ⟶ Q.x) :
    (∃ g : P ⟶ Q, g.a = f) ↔
      reindexedSectionValue α hα e V β P = V.map f.op (reindexedSectionValue α hα e V β Q) := by
  rw [reindexedLift_hom_iff α hα f, reindexedLiftSection_hom_iff α hα e f,
    ← (β P.x).injective.eq_iff, hβ]
  simp only [reindexedSectionValue, Equiv.apply_symm_apply]

/-- The 1-morphism from the 2-fibre product formed along `L` to the category of elements of `V`
which names the section of `V` attached to each object. -/
noncomputable def reindexedSectionFunctor :
    TwoFibreProductOver (K ⋙ c) pY pX L G ⥤ (presheafOfCategories (V ⋙ typeToCat)).obj where
  obj P := ⟨P.x, Discrete.mk (reindexedSectionValue α hα e V β P)⟩
  map f := ⟨f.a, eqToHom (congrArg Discrete.mk
    ((reindexedSectionValue_hom_iff α hα e V β hβ f.a).mp ⟨f, rfl⟩))⟩
  map_id _ := PresheafOfCategories.elements_hom_ext _ _ rfl
  map_comp _ _ := PresheafOfCategories.elements_hom_ext _ _ rfl

attribute [local implicit_reducible] reindexedSectionFunctor reindexedSectionValue

/-- The 2-fibre product formed along `L` is represented by `V`: given a representation of the
2-fibre product formed along `M = K^* L` by a presheaf `N` on the target of `K`, and an
identification of `V` with the restriction of `N` along `K`, naming sections is an equivalence
over the base onto the category of elements of `V`. -/
noncomputable def reindexedSectionEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.fst (K ⋙ c) pY pX L G)
      (presheafOfCategories (V ⋙ typeToCat)).p := by
  let H := reindexedSectionFunctor α hα e V β hβ
  have hH : H ⋙ (presheafOfCategories (V ⋙ typeToCat)).p =
      TwoFibreProductOver.fst (K ⋙ c) pY pX L G := rfl
  have hf : H.Faithful :=
    ⟨fun {P Q} f g h => reindexedLift_hom_ext α hα e f g (congrArg (fun t => t.base) h)⟩
  have hu : H.Full := ⟨fun {P Q} f => by
    have h := Discrete.eq_of_hom f.fiber
    change reindexedSectionValue α hα e V β P =
      V.map f.base.op (reindexedSectionValue α hα e V β Q) at h
    obtain ⟨g, hg⟩ := (reindexedSectionValue_hom_iff α hα e V β hβ f.base).mpr h
    exact ⟨g, PresheafOfCategories.elements_hom_ext _ _ hg⟩⟩
  refine equivalenceOverOfVerticalPreimages H hH ?_
  rintro ⟨T, s⟩
  obtain ⟨P, hP, hs⟩ := reindexedLiftSection_surjective α hα e T (β T s.as)
  have he : H.obj P = (⟨T, s⟩ : (presheafOfCategories (V ⋙ typeToCat)).obj) := by
    cases hP
    change (⟨P.x, Discrete.mk ((β P.x).symm _)⟩ :
      (presheafOfCategories (V ⋙ typeToCat)).obj) = ⟨P.x, s⟩
    rw [hs, Equiv.symm_apply_apply]
    rfl
  exact ⟨P, hP, eqToIso he.symm, IsHomLift.eqToHom_domain_lift_id he.symm rfl⟩

end ReindexedRepresentation

/-! ### Isomorphisms of a 2-fibre product -/

/-- A morphism of a 2-fibre product over a base whose base morphism and whose two components are
isomorphisms is an isomorphism. -/
theorem isIso_twoFibreProductOver_hom {𝒞 𝒳 𝒴 𝒮 : Type*} [Category 𝒞] [Category 𝒳]
    [Category 𝒴] [Category 𝒮] {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {Fn : 𝒳 ⥤ 𝒮} {Gn : 𝒴 ⥤ 𝒮}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 Fn Gn} (t : P ⟶ Q) [IsIso t.hbase] [IsIso t.a]
    [IsIso t.b] : IsIso t := by
  have hta := t.ha
  have htb := t.hb
  have h₁ : Fn.map (inv t.a) ≫ Fn.map t.a = 𝟙 (Fn.obj Q.x) := by
    rw [← Fn.map_comp, IsIso.inv_hom_id, Fn.map_id]
  have h₂ : Gn.map t.b ≫ Gn.map (inv t.b) = 𝟙 (Gn.obj P.y) := by
    rw [← Gn.map_comp, IsIso.hom_inv_id, Gn.map_id]
  refine ⟨⟨{ hbase := inv t.hbase
             a := inv t.a
             b := inv t.b
             ha := IsHomLift.inv p𝒳 t.hbase t.a
             hb := IsHomLift.inv p𝒴 t.hbase t.b
             w := ?_ }, ?_, ?_⟩⟩
  · calc Fn.map (inv t.a) ≫ P.iso.hom
        = Fn.map (inv t.a) ≫ (P.iso.hom ≫ Gn.map t.b) ≫ Gn.map (inv t.b) := by
          rw [Category.assoc, h₂, Category.comp_id]
      _ = Fn.map (inv t.a) ≫ (Fn.map t.a ≫ Q.iso.hom) ≫ Gn.map (inv t.b) := by rw [t.w]
      _ = Q.iso.hom ≫ Gn.map (inv t.b) := by
          rw [← Category.assoc, ← Category.assoc, h₁, Category.id_comp]
  · exact TwoFibreProductOver.Hom.ext' (by simp) (by simp)
  · exact TwoFibreProductOver.Hom.ext' (by simp) (by simp)

end AlgebraicGeometry.Stack

end
