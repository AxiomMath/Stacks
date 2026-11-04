module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GoodDiagramExistenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitDescriptionIsomorphism

/-!
# Stacks 0CPB: spaces of finite type over a Noetherian limit as inverse systems

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces over
a scheme `S` with affine transition morphisms (Situation 0CP6). An algebraic space `X`,
quasi-separated and of finite type over `B`, together with a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

as in Stacks 0CP8 produces the inverse system `(X_{i'})_{i' ≥ i}` of scheme-theoretic images of
`X ⟶ B_{i'} ×_{B_i} W`, with `X = lim X_{i'}` (Stacks 0CP9). Stacks 0CPB observes that Lemmas
0CP7, 0CP9 and 0CPA make the category of algebraic spaces quasi-separated and of finite type over
`B` equivalent to the category of these inverse systems, a morphism of systems being a morphism of
inverse systems over `(B_i)` defined on some tail of the index set, up to shrinking the index set.
In particular two diagrams for the same `X` give canonically isomorphic limit descriptions.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianLimitSystem.FiniteTypeSpaces`: the category of algebraic
  spaces quasi-separated and of finite type over `B`, a full subcategory of the spaces over `B`.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.LimitDescription`: a space of `FiniteTypeSpaces`
  with a diagram as in Stacks 0CP8, standing for the inverse system of Stacks 0CP9 it produces.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.LimitDescription.TailHom`: a morphism
  `(f_i)_{i ≥ i₀}` of the two inverse systems over `(B_i)_{i ≥ i₀}` on a tail of the index set.
  Two of them are identified when they agree at every sufficiently late stage, and the resulting
  germs are the morphisms of the category `LimitDescription`.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.limitFunctor`: the functor taking a system to
  its limit, and a germ of morphisms of systems to the morphism of limits it induces.

## Main results

* `AlgebraicGeometry.Space.NoetherianLimitSystem.isEquivalence_limitFunctor`: **Stacks 0CPB**,
  the limit functor is an equivalence of categories. It is faithful and full by Stacks 0CPA, and
  essentially surjective by Stacks 0CP7.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.limitEquivalence`: the equivalence itself.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.exists_iso_imageSystem`: **the example of
  Stacks 0CPB**: the inverse systems of two diagrams for the same `X` become isomorphic, over
  `(B_i)` and compatibly with the maps from `X`, after shrinking the index set; and the
  isomorphism is canonical, every morphism of the two systems inducing `id_X` agreeing with it at
  all late stages.

## Implementation notes

Situation 0CP6 is `AlgebraicGeometry.Space.NoetherianSpaceSystem`, whose limit `B` is constructed;
its field `indexSize` is the chapter's convention that the index set be small for the site, which
the library's form of Stacks 0CP9 uses.

A morphism of systems is a natural transformation between the restrictions of the two image
systems to the stages above `i₀`, through `CategoryTheory.Over.map`, lying over the base system.
It determines the morphism `f` of limits, which is not part of the data:
`AlgebraicGeometry.Space.NoetherianLimitSystem.LimitDescription.TailHom.limitHom` constructs it,
using that the restriction of a limit cone to a tail is still a limit cone.

## References

* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace NoetherianLimitSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (D : NoetherianLimitSystem B S hS hZ I)

/-- A space over `B` is an algebraic space, quasi-separated and of finite type over `B`. -/
def IsQSFiniteType : ObjectProperty (Over D.limitCone.pt) := fun U =>
  IsAlgebraicSpace B S hS U.left ∧ IsQuasiSeparated B S hS U.hom ∧ IsFiniteType B S hS U.hom

/-- The category of algebraic spaces quasi-separated and of finite type over `B = lim B_i`: a
full subcategory of the spaces over `B`, whose morphisms are the morphisms over `B`. -/
abbrev FiniteTypeSpaces := (IsQSFiniteType D).FullSubcategory

/-- An algebraic space `X` quasi-separated and of finite type over `B` together with a diagram as
in Stacks 0CP8; it stands for the inverse system `(X_{i'})_{i' ≥ i}` of scheme-theoretic images
which Stacks 0CP9 attaches to the diagram, `AlgebraicGeometry.Space.GoodDiagram.imageSystem`. -/
structure LimitDescription where
  /-- The space `X ⟶ B`. -/
  space : FiniteTypeSpaces D
  /-- The diagram `X ⟶ W ⟶ B_i` of Stacks 0CP8. -/
  diagram : GoodDiagram B S hS hZ D space.obj.hom

namespace LimitDescription

variable {D}

/-- A morphism `(f_i)_{i ≥ i₀}` of the inverse systems of scheme-theoretic images of two
diagrams, defined on the tail of stages above `i₀`, each `f_i : X_i ⟶ Y_i` lying over the stage
`B_i`. -/
structure TailHom (P Q : LimitDescription D) where
  /-- The stage `i₀` above which the morphism is defined. -/
  index : I
  /-- The stage `i₀` lies above the stage of the diagram of the source. -/
  le_source : P.diagram.index ≤ index
  /-- The stage `i₀` lies above the stage of the diagram of the target. -/
  le_target : Q.diagram.index ≤ index
  /-- The components `f_i : X_i ⟶ Y_i` for `i ≥ i₀`, natural in `i`. -/
  maps : Over.map (homOfLE le_source).op ⋙ GoodDiagram.imageSystem P.diagram ⟶
    Over.map (homOfLE le_target).op ⋙ GoodDiagram.imageSystem Q.diagram
  /-- Each component `f_i` is a morphism over the stage `B_i`. -/
  over_base : ∀ j : Over (op index),
    maps.app j ≫ (GoodDiagram.stageImage Q.diagram ((Over.map (homOfLE le_target).op).obj j)).ι ≫
        pullback.fst _ _ =
      (GoodDiagram.stageImage P.diagram ((Over.map (homOfLE le_source).op).obj j)).ι ≫
        pullback.fst _ _

namespace TailHom

variable {P Q R : LimitDescription D}

/-- The component `f_i : X_i ⟶ Y_i` of a morphism of systems at a stage `i ≥ i₀`. -/
abbrev app (F : TailHom P Q) (i : I) (h : F.index ≤ i) :
    (GoodDiagram.imageSystem P.diagram).obj (Over.mk (homOfLE (F.le_source.trans h)).op) ⟶
      (GoodDiagram.imageSystem Q.diagram).obj (Over.mk (homOfLE (F.le_target.trans h)).op) :=
  F.maps.app (Over.mk (homOfLE h).op)

/-- Two morphisms of systems agree at every sufficiently late stage. -/
def EventuallyEq (F F' : TailHom P Q) : Prop :=
  ∃ (k : I) (hF : F.index ≤ k) (hF' : F'.index ≤ k),
    ∀ (i : I) (hi : k ≤ i), F.app i (hF.trans hi) = F'.app i (hF'.trans hi)

/-- Agreeing at all late stages is an equivalence relation, by directedness of the index set. -/
theorem eventuallyEq_equivalence : Equivalence (EventuallyEq (P := P) (Q := Q)) where
  refl F := ⟨F.index, le_rfl, le_rfl, fun _ _ => rfl⟩
  symm := fun ⟨k, hF, hF', h⟩ => ⟨k, hF', hF, fun i hi => (h i hi).symm⟩
  trans := fun ⟨k, hF, hF', h⟩ ⟨k', hG, hG', h'⟩ => by
    obtain ⟨m, hkm, hk'm⟩ := exists_ge_ge k k'
    exact ⟨m, hF.trans hkm, hG'.trans hk'm, fun i hi =>
      (h i (hkm.trans hi)).trans (h' i (hk'm.trans hi))⟩

/-- The setoid of morphisms of systems up to agreement at late stages. -/
def setoid (P Q : LimitDescription D) : Setoid (TailHom P Q) :=
  ⟨EventuallyEq, eventuallyEq_equivalence⟩

/-- The restriction of a morphism of systems to a later tail. -/
noncomputable def restrict (F : TailHom P Q) {k : I} (h : F.index ≤ k) : TailHom P Q where
  index := k
  le_source := F.le_source.trans h
  le_target := F.le_target.trans h
  maps :=
    { app j := F.maps.app ((Over.map (homOfLE h).op).obj j)
      naturality _ _ v := F.maps.naturality ((Over.map (homOfLE h).op).map v) }
  over_base j := F.over_base ((Over.map (homOfLE h).op).obj j)

/-- The component of a restricted morphism of systems at a stage `i` is that of the original. -/
@[simp]
lemma restrict_app (F : TailHom P Q) {k : I} (h : F.index ≤ k) (i : I) (hi : k ≤ i) :
    (F.restrict h).app i hi = F.app i (h.trans hi) := rfl

/-- A morphism of systems agrees with its restriction to a later tail. -/
lemma eventuallyEq_restrict (F : TailHom P Q) {k : I} (h : F.index ≤ k) :
    EventuallyEq (F.restrict h) F :=
  ⟨k, le_rfl, h, fun _ _ => rfl⟩

/-- The identity morphism of the inverse system of a diagram. -/
noncomputable def id (P : LimitDescription D) : TailHom P P where
  index := P.diagram.index
  le_source := le_rfl
  le_target := le_rfl
  maps := 𝟙 _
  over_base _ := Category.id_comp _

/-- Every component of the identity morphism of systems is an identity. -/
@[simp]
lemma id_app (P : LimitDescription D) (i : I) (hi : P.diagram.index ≤ i) :
    (id P).app i hi = 𝟙 _ := rfl

/-- The composite of two morphisms of systems, on a given common tail. -/
noncomputable def compOfLE (F : TailHom P Q) (G : TailHom Q R) {k : I} (hF : F.index ≤ k)
    (hG : G.index ≤ k) : TailHom P R where
  index := k
  le_source := F.le_source.trans hF
  le_target := G.le_target.trans hG
  maps := (F.restrict hF).maps ≫ (G.restrict hG).maps
  over_base j := (Category.assoc _ _ _).trans
    ((congrArg ((F.restrict hF).maps.app j ≫ ·) ((G.restrict hG).over_base j)).trans
      ((F.restrict hF).over_base j))

/-- The composite of two morphisms of systems, defined on a common tail. -/
noncomputable def comp (F : TailHom P Q) (G : TailHom Q R) : TailHom P R :=
  compOfLE F G (exists_ge_ge F.index G.index).choose_spec.1
    (exists_ge_ge F.index G.index).choose_spec.2

/-- The tail of a composite starts after the tail of its first factor. -/
lemma le_comp_index_left (F : TailHom P Q) (G : TailHom Q R) : F.index ≤ (F.comp G).index :=
  (exists_ge_ge F.index G.index).choose_spec.1

/-- The tail of a composite starts after the tail of its second factor. -/
lemma le_comp_index_right (F : TailHom P Q) (G : TailHom Q R) : G.index ≤ (F.comp G).index :=
  (exists_ge_ge F.index G.index).choose_spec.2

/-- The component of a composite of morphisms of systems at a stage `i` is the composite of the
components at `i`. -/
@[simp]
lemma comp_app (F : TailHom P Q) (G : TailHom Q R) (i : I) (hi : (F.comp G).index ≤ i) :
    (F.comp G).app i hi =
      F.app i ((le_comp_index_left F G).trans hi) ≫ G.app i ((le_comp_index_right F G).trans hi) :=
  rfl

/-- Composition of morphisms of systems respects agreement at late stages. -/
lemma comp_congr {F F' : TailHom P Q} {G G' : TailHom Q R} (hF : EventuallyEq F F')
    (hG : EventuallyEq G G') : EventuallyEq (F.comp G) (F'.comp G') := by
  obtain ⟨k, hk, hk', h⟩ := hF
  obtain ⟨l, hl, hl', h'⟩ := hG
  obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
  obtain ⟨n, hmn, hcn⟩ := exists_ge_ge m (F.comp G).index
  obtain ⟨o, hno, hco⟩ := exists_ge_ge n (F'.comp G').index
  refine ⟨o, hcn.trans hno, hco, fun i hi => ?_⟩
  rw [comp_app, comp_app, h i (hkm.trans (hmn.trans (hno.trans hi))),
    h' i (hlm.trans (hmn.trans (hno.trans hi)))]

end TailHom

/-- **The category of the inverse systems of Stacks 0CP9.** Its objects are the inverse systems
of scheme-theoretic images produced by diagrams as in Stacks 0CP8, and its morphisms are the
morphisms of inverse systems over `(B_i)` defined on a tail of the index set, up to shrinking the
index set: two are identified when they agree at every sufficiently late stage. -/
noncomputable instance category : Category (LimitDescription D) where
  Hom P Q := Quotient (TailHom.setoid P Q)
  id P := ⟦TailHom.id P⟧
  comp := Quotient.map₂ TailHom.comp fun _ _ hF _ _ hG => TailHom.comp_congr hF hG
  id_comp := by
    rintro P Q ⟨F⟩
    exact Quotient.sound (show TailHom.EventuallyEq ((TailHom.id P).comp F) F from
      ⟨((TailHom.id P).comp F).index, le_rfl, TailHom.le_comp_index_right _ _,
        fun _ _ => Category.id_comp _⟩)
  comp_id := by
    rintro P Q ⟨F⟩
    exact Quotient.sound (show TailHom.EventuallyEq (F.comp (TailHom.id Q)) F from
      ⟨(F.comp (TailHom.id Q)).index, le_rfl, TailHom.le_comp_index_left _ _,
        fun _ _ => Category.comp_id _⟩)
  assoc := by
    rintro P Q R T ⟨F⟩ ⟨G⟩ ⟨H⟩
    obtain ⟨m, h₁, h₂⟩ := exists_ge_ge ((F.comp G).comp H).index (F.comp (G.comp H)).index
    exact Quotient.sound (show TailHom.EventuallyEq ((F.comp G).comp H) (F.comp (G.comp H)) from
      ⟨m, h₁, h₂, fun _ _ => Category.assoc _ _ _⟩)

/-- The canonical cone from `X` to its inverse system, restricted to the stages above `k`, is a
limit cone: Stacks 0CP9, and initiality of the inclusion of a tail of the index set. -/
noncomputable def isLimitTail (P : LimitDescription D) {k : I} (h : P.diagram.index ≤ k) :
    IsLimit ((GoodDiagram.imageCone P.diagram).whisker (Over.map (homOfLE h).op)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm
    (GoodDiagram.isLimit_imageCone_of_algebraicLimit P.diagram P.space.property.1)

/-- Two morphisms to `X` which agree after the projections to all sufficiently late stages of its
inverse system are equal. -/
lemma hom_ext_of_eventually (P : LimitDescription D) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {m₁ m₂ : Z ⟶ P.space.obj.left} (k : I)
    (h : ∀ (i : I) (hi : P.diagram.index ≤ i), k ≤ i →
      m₁ ≫ (GoodDiagram.imageCone P.diagram).π.app (Over.mk (homOfLE hi).op) =
        m₂ ≫ (GoodDiagram.imageCone P.diagram).π.app (Over.mk (homOfLE hi).op)) :
    m₁ = m₂ := by
  refine GoodDiagram.eq_of_comp_imageCone_π_eq P.diagram m₁ m₂ fun j => ?_
  obtain ⟨i, hji, hki⟩ := exists_ge_ge j.left.unop k
  have hi : P.diagram.index ≤ i := (leOfHom j.hom.unop).trans hji
  let a : (Over.mk (homOfLE hi).op : Over (op P.diagram.index)) ⟶ j :=
    Over.homMk (homOfLE hji).op (Subsingleton.elim _ _)
  rw [← (GoodDiagram.imageCone P.diagram).w a, ← Category.assoc, h i hi hki, Category.assoc]

namespace TailHom

variable {P Q R : LimitDescription D}

/-- The morphism `f : X ⟶ Y` of limits induced by a morphism of systems: `X` maps to the tail of
the inverse system of `Y` through the components `f_i`, and `Y` is the limit of that tail. -/
noncomputable def limitHom (F : TailHom P Q) : P.space.obj.left ⟶ Q.space.obj.left :=
  (isLimitTail Q F.le_target).lift
    ((Cone.postcompose F.maps).obj
      ((GoodDiagram.imageCone P.diagram).whisker (Over.map (homOfLE F.le_source).op)))

/-- The morphism of limits is compatible with the components of the morphism of systems. -/
lemma limitHom_comp_π (F : TailHom P Q) (j : Over (op F.index)) :
    F.limitHom ≫
        (GoodDiagram.imageCone Q.diagram).π.app ((Over.map (homOfLE F.le_target).op).obj j) =
      (GoodDiagram.imageCone P.diagram).π.app ((Over.map (homOfLE F.le_source).op).obj j) ≫
        F.maps.app j :=
  (isLimitTail Q F.le_target).fac _ j

/-- The morphism of limits is compatible with the component `f_i` of the morphism of systems at
each stage `i ≥ i₀`. -/
lemma limitHom_comp_π_app (F : TailHom P Q) (i : I) (hi : F.index ≤ i) :
    F.limitHom ≫ (GoodDiagram.imageCone Q.diagram).π.app
        (Over.mk (homOfLE (F.le_target.trans hi)).op) =
      (GoodDiagram.imageCone P.diagram).π.app (Over.mk (homOfLE (F.le_source.trans hi)).op) ≫
        F.app i hi :=
  F.limitHom_comp_π (Over.mk (homOfLE hi).op)

/-- **Uniqueness of the morphism of limits.** A morphism `X ⟶ Y` compatible with the components
of a morphism of systems at all sufficiently late stages is the induced morphism of limits. -/
lemma limitHom_eq (F : TailHom P Q) (m : P.space.obj.left ⟶ Q.space.obj.left) (k : I)
    (h : ∀ (i : I) (hi : F.index ≤ i), k ≤ i →
      (GoodDiagram.imageCone P.diagram).π.app (Over.mk (homOfLE (F.le_source.trans hi)).op) ≫
          F.app i hi =
        m ≫ (GoodDiagram.imageCone Q.diagram).π.app
          (Over.mk (homOfLE (F.le_target.trans hi)).op)) :
    F.limitHom = m := by
  obtain ⟨k', hk, hF⟩ := exists_ge_ge k F.index
  refine hom_ext_of_eventually Q k' fun i hi hki => ?_
  rw [F.limitHom_comp_π_app i (hF.trans hki), h i (hF.trans hki) (hk.trans hki)]

/-- **The morphism of limits lies over `B`.** Its composite with `Y ⟶ B ⟶ B_i` is computed at a
late stage `i`, where the components of the morphism of systems lie over `B_i`. -/
lemma limitHom_comp_hom (F : TailHom P Q) : F.limitHom ≫ Q.space.obj.hom = P.space.obj.hom := by
  refine D.isLimit.hom_ext fun j => ?_
  obtain ⟨i, hji, hFi⟩ := exists_ge_ge j.unop F.index
  have hπ : D.limitCone.π.app j =
      D.limitCone.π.app (op i) ≫
        D.system.map (homOfLE hji).op :=
    (D.limitCone.w (homOfLE hji).op).symm
  have hcone : ∀ (R : LimitDescription D) (h : R.diagram.index ≤ i),
      R.space.obj.hom ≫ D.limitCone.π.app (op i) =
        (GoodDiagram.imageCone R.diagram).π.app (Over.mk (homOfLE h).op) ≫
          (GoodDiagram.stageImage R.diagram (Over.mk (homOfLE h).op)).ι ≫ pullback.fst _ _ := by
    intro R h
    rw [GoodDiagram.imageCone_π_ι_assoc, GoodDiagram.stageMap_fst]
    rfl
  have hb : F.app i hFi ≫ (GoodDiagram.stageImage Q.diagram
        (Over.mk (homOfLE (F.le_target.trans hFi)).op)).ι ≫ pullback.fst _ _ =
      (GoodDiagram.stageImage P.diagram
        (Over.mk (homOfLE (F.le_source.trans hFi)).op)).ι ≫ pullback.fst _ _ :=
    F.over_base (Over.mk (homOfLE hFi).op)
  have key : (F.limitHom ≫ Q.space.obj.hom) ≫ D.limitCone.π.app (op i) =
      P.space.obj.hom ≫ D.limitCone.π.app (op i) := by
    rw [Category.assoc, hcone Q (F.le_target.trans hFi), ← Category.assoc,
      F.limitHom_comp_π_app i hFi, Category.assoc, hb, hcone P (F.le_source.trans hFi)]
  rw [hπ, ← Category.assoc, ← Category.assoc, key]

/-- A morphism of systems whose morphism of limits is `f` is a morphism of systems inducing `f`
in the sense of Stacks 0CPA. -/
def toSystemMorphism (F : TailHom P Q) {f : P.space.obj.left ⟶ Q.space.obj.left}
    (hf : F.limitHom = f) :
    GoodDiagram.SystemMorphism P.diagram Q.diagram f F.index F.le_source F.le_target where
  maps := F.maps
  over_base := F.over_base
  induces j := by
    subst hf
    exact (F.limitHom_comp_π j).symm

/-- A morphism of systems inducing `f` in the sense of Stacks 0CPA. -/
def ofSystemMorphism {f : P.space.obj.left ⟶ Q.space.obj.left} {i₀ : I}
    {hP : P.diagram.index ≤ i₀} {hQ : Q.diagram.index ≤ i₀}
    (F : GoodDiagram.SystemMorphism P.diagram Q.diagram f i₀ hP hQ) : TailHom P Q where
  index := i₀
  le_source := hP
  le_target := hQ
  maps := F.maps
  over_base := F.over_base

/-- The morphism of systems built from a system morphism inducing `f` has morphism of limits
`f`. -/
lemma limitHom_ofSystemMorphism {f : P.space.obj.left ⟶ Q.space.obj.left} {i₀ : I}
    {hP : P.diagram.index ≤ i₀} {hQ : Q.diagram.index ≤ i₀}
    (F : GoodDiagram.SystemMorphism P.diagram Q.diagram f i₀ hP hQ) :
    (ofSystemMorphism F).limitHom = f :=
  (ofSystemMorphism F).limitHom_eq f i₀ fun _ hi _ => F.induces (Over.mk (homOfLE hi).op)

/-- Morphisms of systems agreeing at late stages induce the same morphism of limits. -/
lemma limitHom_congr {F F' : TailHom P Q} (h : EventuallyEq F F') :
    F.limitHom = F'.limitHom := by
  obtain ⟨k, hk, hk', h⟩ := h
  refine F.limitHom_eq F'.limitHom k fun i hi hki => ?_
  rw [h i hki, F'.limitHom_comp_π_app i (hk'.trans hki)]

/-- The identity morphism of systems induces the identity morphism of limits. -/
lemma limitHom_id (P : LimitDescription D) : (id P).limitHom = 𝟙 _ :=
  (id P).limitHom_eq _ P.diagram.index fun _ _ _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The morphism of limits induced by a composite of morphisms of systems is the composite of the
induced morphisms of limits. -/
lemma limitHom_comp (F : TailHom P Q) (G : TailHom Q R) :
    (F.comp G).limitHom = F.limitHom ≫ G.limitHom := by
  refine (F.comp G).limitHom_eq _ (F.comp G).index fun i hi _ => ?_
  rw [comp_app, ← Category.assoc, ← F.limitHom_comp_π_app, Category.assoc,
    ← G.limitHom_comp_π_app, Category.assoc]

end TailHom

end LimitDescription

/-- **The limit functor.** It takes the inverse system of a diagram as in Stacks 0CP8 to its
limit `X`, and a morphism of systems, up to shrinking the index set, to the morphism of limits it
induces. -/
noncomputable def limitFunctor : LimitDescription D ⥤ FiniteTypeSpaces D where
  obj P := P.space
  map {P Q} := Quotient.lift
    (fun F : LimitDescription.TailHom P Q =>
      ObjectProperty.homMk (Over.homMk F.limitHom F.limitHom_comp_hom))
    fun _ _ h => ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (LimitDescription.TailHom.limitHom_congr h))
  map_id P := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (LimitDescription.TailHom.limitHom_id P))
  map_comp := by
    rintro P Q R ⟨F⟩ ⟨G⟩
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (LimitDescription.TailHom.limitHom_comp F G))

/-- The limit functor sends the class of a morphism of systems to its morphism of limits. -/
lemma limitFunctor_map_hom_left {P Q : LimitDescription D} (F : LimitDescription.TailHom P Q) :
    ((limitFunctor D).map (⟦F⟧ : P ⟶ Q)).hom.left = F.limitHom := rfl

/-- **Stacks 0CPA, existence: the limit functor is full.** A morphism `f : X ⟶ Y` over `B` is
induced by a morphism of the inverse systems on some tail of the index set. -/
instance full_limitFunctor : (limitFunctor D).Full where
  map_surjective {P Q} g := by
    obtain ⟨i₀, hP, hQ, ⟨F⟩⟩ := GoodDiagram.exists_systemMorphism_of_algebraicLimit
      P.space.property.1 P.space.property.2.1 g.hom.left (Over.w g.hom) P.diagram Q.diagram
    exact ⟨⟦LimitDescription.TailHom.ofSystemMorphism F⟧, ObjectProperty.hom_ext _
      (Over.OverMorphism.ext (LimitDescription.TailHom.limitHom_ofSystemMorphism F))⟩

/-- **Stacks 0CPA, uniqueness: the limit functor is faithful.** Two morphisms of inverse systems
inducing the same morphism of limits agree at all sufficiently late stages. -/
instance faithful_limitFunctor : (limitFunctor D).Faithful where
  map_injective {P Q} := by
    rintro ⟨F⟩ ⟨F'⟩ h
    have hf : F.limitHom = F'.limitHom := congrArg (fun g => g.hom.left) h
    obtain ⟨k, hk, hk'⟩ := exists_ge_ge F.index F'.index
    obtain ⟨i₃, hi₃, heq⟩ := GoodDiagram.eventually_eq_systemMorphism_of_algebraicLimit
      P.space.property.1 P.space.property.2.1
      ((F.restrict hk).toSystemMorphism
        (LimitDescription.TailHom.limitHom_congr (F.eventuallyEq_restrict hk)))
      ((F'.restrict hk').toSystemMorphism
        ((LimitDescription.TailHom.limitHom_congr (F'.eventuallyEq_restrict hk')).trans hf.symm))
    exact Quotient.sound ⟨i₃, hk.trans hi₃, hk'.trans hi₃, fun i hi =>
      heq (Over.mk (homOfLE (hi₃.trans hi)).op) hi⟩

/-- **Stacks 0CP7: the limit functor is essentially surjective.** Every algebraic space
quasi-separated and of finite type over `B` has a diagram as in Stacks 0CP8, hence is the limit of
the inverse system of that diagram. -/
instance essSurj_limitFunctor : (limitFunctor D).EssSurj where
  mem_essImage U :=
    ⟨⟨U, (D.nonempty_goodDiagram U.obj.hom U.property.1 U.property.2.1 U.property.2.2).some⟩,
      ⟨Iso.refl _⟩⟩

/-- **Stacks 0CPB.** In Situation 0CP6, the category of algebraic spaces quasi-separated and of
finite type over `B = lim B_i` is equivalent to the category of the inverse systems of algebraic
spaces over `(B_i)` produced by Stacks 0CP9 from a diagram as in Stacks 0CP8, whose morphisms are
the morphisms of inverse systems over `(B_i)` on a tail of the index set, up to shrinking the
index set. The equivalence takes a system to its limit: it is essentially surjective by
Stacks 0CP7, full by the existence half and faithful by the uniqueness half of Stacks 0CPA. -/
@[stacks 0CPB "the category of algebraic spaces quasi-separated and of finite type over B is
  equivalent to the category of the inverse systems over (B_i) that 0CP9 produces from the
  diagrams (0CP8), up to shrinking the index set"]
theorem isEquivalence_limitFunctor : (limitFunctor D).IsEquivalence := {}

/-- The equivalence of Stacks 0CPB between the inverse systems of Stacks 0CP9 and the algebraic
spaces quasi-separated and of finite type over `B`. -/
noncomputable def limitEquivalence : LimitDescription D ≌ FiniteTypeSpaces D :=
  have := isEquivalence_limitFunctor D
  (limitFunctor D).asEquivalence

/-- **Stacks 0CPB, the example, in the category of systems.** Two diagrams as in Stacks 0CP8 for
the same `X ⟶ B` give isomorphic inverse systems, by a unique isomorphism of germs of morphisms of
systems inducing `id_X` on the limits. -/
theorem existsUnique_iso_limitDescription (U : FiniteTypeSpaces D)
    (G₁ G₂ : GoodDiagram B S hS hZ D U.obj.hom) :
    ∃! e : (⟨U, G₁⟩ : LimitDescription D) ≅ ⟨U, G₂⟩, (limitFunctor D).map e.hom = 𝟙 U := by
  let hff : (limitFunctor D).FullyFaithful := .ofFullyFaithful _
  let e₀ : (⟨U, G₁⟩ : LimitDescription D) ≅ ⟨U, G₂⟩ :=
    hff.preimageIso (X := ⟨U, G₁⟩) (Y := ⟨U, G₂⟩) (Iso.refl U)
  have hpre : (limitFunctor D).map e₀.hom = 𝟙 U :=
    hff.map_preimage (X := (⟨U, G₁⟩ : LimitDescription D)) (Y := ⟨U, G₂⟩) (𝟙 U)
  exact ⟨e₀, hpre, fun e he =>
    Iso.ext ((limitFunctor D).map_injective (he.trans hpre.symm))⟩

/-- **Stacks 0CPB, the example.** Let `X` be an algebraic space quasi-separated and of finite type
over `B`, and let `X ⟶ W₁ ⟶ B_{i₁}` and `X ⟶ W₂ ⟶ B_{i₂}` be two diagrams as in Stacks 0CP8. Then,
up to shrinking the index set to the stages above some `i₀`, the corresponding limit descriptions
`X = lim X_{1,i}` and `X = lim X_{2,i}` of Stacks 0CP9 are isomorphic: there is an isomorphism of
inverse systems `(X_{1,i})_{i ≥ i₀} ≅ (X_{2,i})_{i ≥ i₀}` over `(B_i)_{i ≥ i₀}`, compatible in both
directions with the maps from `X`, that is, with limit `id_X`. The isomorphism is canonical: every
morphism of the two systems over `(B_i)` on any tail whose limit is `id_X` agrees with it at all
sufficiently late stages.

It is obtained by applying Stacks 0CPA to `id_X` in both directions: existence gives the two
morphisms of systems, and uniqueness shows that their composites agree with the identities at
late stages. -/
@[stacks 0CPB "the example: two limit descriptions of X are canonically isomorphic, after
  shrinking the index set"]
theorem exists_iso_imageSystem (U : FiniteTypeSpaces D)
    (G₁ G₂ : GoodDiagram B S hS hZ D U.obj.hom) :
    ∃ (i₀ : I) (h₁ : G₁.index ≤ i₀) (h₂ : G₂.index ≤ i₀)
      (e : Over.map (homOfLE h₁).op ⋙ GoodDiagram.imageSystem G₁ ≅
        Over.map (homOfLE h₂).op ⋙ GoodDiagram.imageSystem G₂),
      (∀ j : Over (op i₀),
        e.hom.app j ≫ (GoodDiagram.stageImage G₂ ((Over.map (homOfLE h₂).op).obj j)).ι ≫
            pullback.fst _ _ =
          (GoodDiagram.stageImage G₁ ((Over.map (homOfLE h₁).op).obj j)).ι ≫ pullback.fst _ _) ∧
      (∀ j : Over (op i₀),
        e.inv.app j ≫ (GoodDiagram.stageImage G₁ ((Over.map (homOfLE h₁).op).obj j)).ι ≫
            pullback.fst _ _ =
          (GoodDiagram.stageImage G₂ ((Over.map (homOfLE h₂).op).obj j)).ι ≫ pullback.fst _ _) ∧
      (∀ j : Over (op i₀),
        (GoodDiagram.imageCone G₁).π.app ((Over.map (homOfLE h₁).op).obj j) ≫ e.hom.app j =
          (GoodDiagram.imageCone G₂).π.app ((Over.map (homOfLE h₂).op).obj j)) ∧
      (∀ j : Over (op i₀),
        (GoodDiagram.imageCone G₂).π.app ((Over.map (homOfLE h₂).op).obj j) ≫ e.inv.app j =
          (GoodDiagram.imageCone G₁).π.app ((Over.map (homOfLE h₁).op).obj j)) ∧
      ∀ (i₁ : I) (k₁ : G₁.index ≤ i₁) (k₂ : G₂.index ≤ i₁)
        (F : GoodDiagram.SystemMorphism G₁ G₂ (𝟙 U.obj.left) i₁ k₁ k₂),
        ∃ (i₃ : I) (hi₀ : i₀ ≤ i₃) (hi₁ : i₁ ≤ i₃), ∀ (i : I) (hi : i₃ ≤ i),
          F.maps.app (Over.mk (homOfLE (hi₁.trans hi)).op) =
            e.hom.app (Over.mk (homOfLE (hi₀.trans hi)).op) := by
  obtain ⟨a, ha₁, ha₂, E, E', m, ham, hinv⟩ :=
    GoodDiagram.SystemMorphism.exists_systemMorphism_inv_of_algebraicLimit U.property.1
      U.property.2.1 G₁ G₂
  let ER := E.restrict ham
  let ER' := E'.restrict ham
  let e : Over.map (homOfLE (ha₁.trans ham)).op ⋙ GoodDiagram.imageSystem G₁ ≅
      Over.map (homOfLE (ha₂.trans ham)).op ⋙ GoodDiagram.imageSystem G₂ :=
    { hom := ER.maps
      inv := ER'.maps
      hom_inv_id := NatTrans.ext (funext fun j => (hinv (unop j.left) (leOfHom j.hom.unop)).1)
      inv_hom_id := NatTrans.ext (funext fun j => (hinv (unop j.left) (leOfHom j.hom.unop)).2) }
  refine ⟨m, ha₁.trans ham, ha₂.trans ham, e, ER.over_base, ER'.over_base,
    fun j => (ER.induces j).trans (Category.id_comp _),
    fun j => (ER'.induces j).trans (Category.id_comp _), fun i₁ k₁ k₂ F => ?_⟩
  obtain ⟨n, hmn, hi₁n⟩ := exists_ge_ge m i₁
  obtain ⟨i₃, hni₃, h⟩ := GoodDiagram.eventually_eq_systemMorphism_of_algebraicLimit U.property.1
    U.property.2.1 (F.restrict hi₁n) (ER.restrict hmn)
  exact ⟨i₃, hmn.trans hni₃, hi₁n.trans hni₃, fun i hi =>
    h (Over.mk (homOfLE (hni₃.trans hi)).op) hi⟩

end NoetherianLimitSystem

end AlgebraicGeometry.Space

end
