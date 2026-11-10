module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Functoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ReindexedSectionRepresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelocalizedSectionsFibre

/-!
# The fibre of a morphism of finite Hilbert categories is a space of sections

Let `G : 𝒳' ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `F : 𝒳 ⟶ 𝒴` and `F' : 𝒳' ⟶ 𝒴` be 1-morphisms to a third stack and let
`γ : F' ⟶ F ∘ G` be a 2-isomorphism, so that Stacks 05XN produces a canonical 1-morphism
`ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` finite Hilbert categories. Fix an object
`ξ = (U, Z, y, x, α)` of `ℋ_d(𝒳/𝒴)`, and suppose the fibre of `G` over the scheme-valued point
of `𝒳` determined by `x` is represented by a presheaf `W` on the big fppf site of `Z`. This file
identifies the fibre of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over `ξ` with the space of sections over `U` of
`W ⟶ Z`, that is with `AlgebraicGeometry.Space.sectionSpace`.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.universalFamily`: the scheme-valued point of
  `ℋ_d(𝒳/𝒴)` over the base of an object, given by the 2-Yoneda lemma.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.sourcePoint`: the scheme-valued point of `𝒳` over
  the cover of an object, given by the 2-Yoneda lemma applied to its object of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace`: the fibre
  of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over an object `ξ` is equivalent, over the big fppf site of the base
  of `ξ`, to the category of elements of the space of sections of `W ⟶ Z` over `U`.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.universalFamily_comp` and
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.sourcePoint_comp`: the two scheme-valued points
  are 1-morphisms over the site.

## References

* [Stacks Project, Tag 05YG](https://stacks.math.columbia.edu/tag/05YG)
* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v₁ u₁

namespace AlgebraicGeometry.Stack

/-! ### Sections of a relocalized presheaf -/

section Relocalize

variable {C : Type*} [Category.{u} C] {U Z : C} (q : Z ⟶ U) (W : (Over Z)ᵒᵖ ⥤ Type u)
  (w : (OverShriek.relocalizePresheafFunctor q).obj W ⟶ yoneda.obj (Over.mk q))
  (hw : ∀ T s, (w.app (op T) s).left = s.val.fst)

end Relocalize

/-! ### Representation of a reindexed 2-fibre product -/

section ReindexedRepresentation

variable {C D E X Y : Type*} [Category C] [Category D] [Category E] [Category X] [Category Y]
  {c : E ⥤ C} {pX : X ⥤ C} {pY : Y ⥤ C} {K : D ⥤ E} {L : D ⥤ X} {M : E ⥤ X} {G : Y ⥤ X}
  (α : L ≅ K ⋙ M) (hα : ∀ T, pX.IsHomLift (𝟙 (c.obj (K.obj T))) (α.hom.app T))

attribute [local implicit_reducible] reindexedLiftObj

attribute [local implicit_reducible] reindexedLiftMap

variable {N : Eᵒᵖ ⥤ Type u}
  (e : StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.fst c pY pX M G)
    (presheafOfCategories (N ⋙ typeToCat)).p)

variable (V : Dᵒᵖ ⥤ Type u) (β : ∀ T, V.obj (op T) ≃ N.obj (op (K.obj T)))
  (hβ : ∀ {T T'} (f : T ⟶ T') (s : V.obj (op T')),
    β T (V.map f.op s) = N.map (K.map f).op (β T' s))

attribute [local implicit_reducible] reindexedSectionFunctor reindexedSectionValue

end ReindexedRepresentation

/-! ### Comparison morphisms of a square whose target column is an identity -/

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳' 𝒳 𝒴 : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory}

/-- The component at an object `x` of `𝒳'` of the inverse of a 2-isomorphism `γ : F' ⟶ F ∘ G`, as a
morphism `F (G x) ⟶ F' x` of `𝒴`. It is `γ.inv.app x`. -/
private def squareComparisonId
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (x : 𝒳'.toBasedCategory.obj) : F.obj (G.obj x) ⟶ F'.obj x :=
  γ.inv.app x

/-- The component at an object `x` of `𝒳'` of a 2-isomorphism `γ : F' ⟶ F ∘ G`, as a morphism
`F' x ⟶ F (G x)` of `𝒴`. It is `γ.hom.app x`. -/
private def squareComparisonIdInv
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (x : 𝒳'.toBasedCategory.obj) : F'.obj x ⟶ F.obj (G.obj x) :=
  γ.hom.app x

/-- The two comparison morphisms at an object of `𝒳'` are mutually inverse, one way round. -/
private theorem squareComparisonId_comp
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (x : 𝒳'.toBasedCategory.obj) :
    squareComparisonId γ x ≫ squareComparisonIdInv γ x = 𝟙 (F.obj (G.obj x)) :=
  congrArg (fun η => η.app x) γ.inv_hom_id

/-- The two comparison morphisms at an object of `𝒳'` are mutually inverse, the other way
round. -/
private theorem squareComparisonIdInv_comp
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (x : 𝒳'.toBasedCategory.obj) :
    squareComparisonIdInv γ x ≫ squareComparisonId γ x = 𝟙 (F'.obj x) :=
  congrArg (fun η => η.app x) γ.hom_inv_id

/-- Naturality of the comparison morphisms of the 2-commutative square. -/
private theorem squareComparisonIdInv_naturality
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    {x y : 𝒳'.toBasedCategory.obj} (f : x ⟶ y) :
    F'.map f ≫ squareComparisonIdInv γ y = squareComparisonIdInv γ x ≫ F.map (G.map f) :=
  γ.hom.naturality f

/-- The comparison morphisms of the 2-commutative square lie over identities. -/
private theorem isHomLift_squareComparisonIdInv
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    {x : 𝒳'.toBasedCategory.obj} {U : BigFppfOver B S hS}
    (hx : 𝒳'.toBasedCategory.p.obj x = U) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 U) (squareComparisonIdInv γ x) :=
  γ.hom.isHomLift hx

end Comparison

/-! ### The fibre of the induced 1-morphism of relative finite Hilbert categories -/

section HilbertMap

attribute [local implicit_reducible] BasedFunctor.comp BasedFunctor.id BasedCategory.ofFunctor
  finiteHilbertCategory finiteHilbertProjection squareComparison mapRelativeFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)
  (𝒳' 𝒳 𝒴 : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
  (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
  (G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory)
  (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)

/-- The functor remembering only the object of `𝒳` lying over the cover. -/
private def finiteHilbertSource :
    FiniteHilbert.Object B S hS 𝒳 𝒴 F d ⥤ 𝒳.toBasedCategory.obj where
  obj P := P.x
  map φ := φ.a

/-- The functor remembering only the cover. -/
private def finiteHilbertCover :
    FiniteHilbert.Object B S hS 𝒳 𝒴 F d ⥤ BigFppfOver B S hS where
  obj P := P.Z
  map φ := φ.g


/-- An object of `ℋ_d(𝒳/𝒴)` whose object of `𝒳` is vertically isomorphic to one coming from `𝒳'`,
read as an object of `ℋ_d(𝒳'/𝒴)`: keep the cover and the object of `𝒴`, replace the object of `𝒳`
by the one of `𝒳'`, and transport the identification across the isomorphism and the given
2-isomorphism. -/
private def replaceSource (P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d)
    (x' : 𝒳'.toBasedCategory.obj) (i : P.x ≅ G.obj x')
    (hi : 𝒳.toBasedCategory.p.IsHomLift (𝟙 P.Z) i.hom) :
    FiniteHilbert.Object B S hS 𝒳' 𝒴 F' d where
  U := P.U
  Z := P.Z
  q := P.q
  finiteLocallyFree := P.finiteLocallyFree
  y := P.y
  y_over := P.y_over
  x := x'
  x_over := (G.w_obj x').symm.trans (by
    have := hi
    exact IsHomLift.codomain_eq _ (𝟙 P.Z) i.hom)
  α := squareComparisonIdInv γ x' ≫ F.map i.inv ≫ P.α
  α_over := by
    have := hi
    have hxi : 𝒳.toBasedCategory.p.IsHomLift (𝟙 P.Z) i.inv := IsHomLift.lift_id_inv _ _ i
    have hx' : 𝒳'.toBasedCategory.p.obj x' = P.Z :=
      (G.w_obj x').symm.trans (IsHomLift.codomain_eq _ (𝟙 P.Z) i.hom)
    have hγ : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (squareComparisonIdInv γ x') :=
      isHomLift_squareComparisonIdInv γ hx'
    have hα := P.α_over
    have hFi : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (F.map i.inv) :=
      BasedFunctor.preserves_isHomLift F _ _
    have hcomp := IsHomLift.comp_lift_id_left 𝒴.toBasedCategory.p P.q P.α (F.map i.inv)
    exact IsHomLift.comp_lift_id_left 𝒴.toBasedCategory.p P.q (F.map i.inv ≫ P.α)
      (squareComparisonIdInv γ x')

/-- The vertical isomorphism of `ℋ_d(𝒳/𝒴)` identifying an object with the image under the induced
1-morphism of the object of `ℋ_d(𝒳'/𝒴)` built from it by
`AlgebraicGeometry.Stack.replaceSource`. -/
private def replaceSourceIso (P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d)
    (x' : 𝒳'.toBasedCategory.obj) (i : P.x ≅ G.obj x')
    (hi : 𝒳.toBasedCategory.p.IsHomLift (𝟙 P.Z) i.hom) :
    P ≅ (mapRelativeFunctor B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).obj
      (replaceSource B S hS d 𝒳' 𝒳 𝒴 F' F G γ P x' i hi) :=
  { hom :=
      { f := 𝟙 P.U
        g := 𝟙 P.Z
        square := IsPullback.id_horiz P.q
        b := 𝟙 P.y
        b_over := IsHomLift.id P.y_over
        a := i.hom
        a_over := hi
        compatible := (show F.map i.hom ≫ squareComparisonId γ x' ≫ squareComparisonIdInv γ x' ≫
            F.map i.inv ≫ P.α = P.α ≫ 𝟙 P.y by
          rw [← Category.assoc (squareComparisonId γ x'), squareComparisonId_comp, Category.id_comp,
            ← Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id, Category.id_comp,
            Category.comp_id]) }
    inv :=
      { f := 𝟙 P.U
        g := 𝟙 P.Z
        square := IsPullback.id_horiz P.q
        b := 𝟙 P.y
        b_over := IsHomLift.id P.y_over
        a := i.inv
        a_over := by
          have := hi
          exact IsHomLift.lift_id_inv 𝒳.toBasedCategory.p P.Z i
        compatible := (show F.map i.inv ≫ P.α = (squareComparisonId γ x' ≫
            squareComparisonIdInv γ x' ≫ F.map i.inv ≫ P.α) ≫ 𝟙 P.y by
          rw [Category.comp_id, ← Category.assoc (squareComparisonId γ x'), squareComparisonId_comp,
            Category.id_comp]) }
    hom_inv_id := FiniteHilbert.Hom.ext (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _) i.hom_inv_id
    inv_hom_id := FiniteHilbert.Hom.ext (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _) i.inv_hom_id }

variable {B S hS d 𝒳' 𝒳 𝒴 F' F G γ}
variable {D : Type*} [Category D] (J : D ⥤ FiniteHilbert.Object B S hS 𝒳 𝒴 F d)

/-- The 2-fibre product of a family of objects of `ℋ_d(𝒳/𝒴)` with `𝒳'` over `𝒳`, taken over the
big fppf site: an object is a point of the family together with an object of `𝒳'` and a vertical
identification of its image in `𝒳` with the object of `𝒳` carried by the family. -/
private abbrev SourceLift :=
  TwoFibreProductOver (J ⋙ finiteHilbertCover B S hS d 𝒳 𝒴 F)
    𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p
    (J ⋙ finiteHilbertSource B S hS d 𝒳 𝒴 F) G.toFunctor

/-- The comparison isomorphism of an object of `AlgebraicGeometry.Stack.SourceLift` is vertical
over the cover of the object of `ℋ_d(𝒳/𝒴)` it sits above. -/
private theorem sourceLift_vertical (P : SourceLift (G := G) J) :
    𝒳.toBasedCategory.p.IsHomLift (𝟙 (J.obj P.x).Z) P.iso.hom := by
  have h : (J.obj P.x).Z = P.base := P.hx
  rw [h]
  exact P.vertical

/-- The object of `ℋ_d(𝒳'/𝒴)` attached to an object of `AlgebraicGeometry.Stack.SourceLift`. -/
private def sourceLiftObject (P : SourceLift (G := G) J) :
    FiniteHilbert.Object B S hS 𝒳' 𝒴 F' d :=
  replaceSource B S hS d 𝒳' 𝒳 𝒴 F' F G γ (J.obj P.x) P.y P.iso (sourceLift_vertical J P)

attribute [local implicit_reducible] sourceLiftObject replaceSource replaceSourceIso
  finiteHilbertSource finiteHilbertCover

/-- The `𝒳'`-component of a morphism of `AlgebraicGeometry.Stack.SourceLift` lies over the cover
component of the morphism of the family it sits above. -/
private theorem sourceLift_hom_over {P Q : SourceLift (G := G) J} (φ : P ⟶ Q) :
    𝒳'.toBasedCategory.p.IsHomLift (J.map φ.a).g φ.b := by
  have hb := φ.hb
  apply IsHomLift.of_fac' _ _ _ (P.hy.trans P.hx.symm) (Q.hy.trans Q.hx.symm)
  rw [IsHomLift.fac' _ φ.hbase φ.b]
  change eqToHom P.hy ≫ φ.hbase ≫ eqToHom Q.hy.symm = _
  rw [φ.hbase_eq]
  simp [finiteHilbertCover]

/-- The morphism of `ℋ_d(𝒳'/𝒴)` attached to a morphism of
`AlgebraicGeometry.Stack.SourceLift`. -/
private def sourceLiftMap {P Q : SourceLift (G := G) J} (φ : P ⟶ Q) :
    sourceLiftObject (F' := F') (γ := γ) J P ⟶ sourceLiftObject (F' := F') (γ := γ) J Q where
  f := (J.map φ.a).f
  g := (J.map φ.a).g
  square := (J.map φ.a).square
  b := (J.map φ.a).b
  b_over := (J.map φ.a).b_over
  a := φ.b
  a_over := sourceLift_hom_over J φ
  compatible := (show F'.map φ.b ≫ squareComparisonIdInv γ Q.y ≫ F.map Q.iso.inv ≫ (J.obj Q.x).α =
      (squareComparisonIdInv γ P.y ≫ F.map P.iso.inv ≫ (J.obj P.x).α) ≫ (J.map φ.a).b by
    have hφ : (J.map φ.a).a ≫ Q.iso.hom = P.iso.hom ≫ G.map φ.b := φ.w
    have hφ' : G.map φ.b ≫ Q.iso.inv = P.iso.inv ≫ (J.map φ.a).a := by
      rw [← cancel_epi P.iso.hom]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun t => t ≫ Q.iso.inv) hφ.symm
    have hn : F'.map φ.b ≫ squareComparisonIdInv γ Q.y =
        squareComparisonIdInv γ P.y ≫ F.map (G.map φ.b) :=
      squareComparisonIdInv_naturality γ φ.b
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← F.toFunctor.map_comp_assoc, hφ', F.map_comp]
    simp only [Category.assoc]
    rw [(J.map φ.a).compatible])

/-- The 1-morphism `AlgebraicGeometry.Stack.SourceLift ⟶ ℋ_d(𝒳'/𝒴)`. -/
private def sourceLiftFunctor :
    SourceLift (G := G) J ⥤ FiniteHilbert.Object B S hS 𝒳' 𝒴 F' d where
  obj := sourceLiftObject (γ := γ) J
  map := sourceLiftMap (γ := γ) J
  map_id P := FiniteHilbert.Hom.ext (congrArg (·.f) (J.map_id P.x))
    (congrArg (·.g) (J.map_id P.x)) (congrArg (·.b) (J.map_id P.x)) rfl
  map_comp φ ψ := FiniteHilbert.Hom.ext (congrArg (·.f) (J.map_comp φ.a ψ.a))
    (congrArg (·.g) (J.map_comp φ.a ψ.a)) (congrArg (·.b) (J.map_comp φ.a ψ.a)) rfl

variable (p : D ⥤ BigFppfOver B S hS) (hJ : J ⋙ finiteHilbertProjection = p)

include hJ in
/-- The base object of a member of a family of objects of `ℋ_d(𝒳/𝒴)` strictly over `p` is the
value of `p`. -/
private theorem familyBase (T : D) : (J.obj T).U = p.obj T :=
  congrArg (fun K => K.obj T) hJ

/-- The 2-fibre product of a family of objects of `ℋ_d(𝒳/𝒴)` with `ℋ_d(𝒳'/𝒴)` over
`ℋ_d(𝒳/𝒴)`, taken over the big fppf site. This is the fibre of the induced 1-morphism along the
family. -/
private abbrev HilbertLift :=
  TwoFibreProductOver p
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F') (d := d))
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    J (mapRelativeFunctor B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ)

/-- The comparison 1-morphism `AlgebraicGeometry.Stack.SourceLift ⟶
AlgebraicGeometry.Stack.HilbertLift`: an object of `𝒳'` identified with the object of `𝒳` carried
by the family gives an object of `ℋ_d(𝒳'/𝒴)` together with an identification of its image with
the member of the family. -/
private def sourceLiftToHilbertLift :
    SourceLift (G := G) J ⥤ HilbertLift (F' := F') (G := G) (γ := γ) J p where
  obj P :=
    { base := p.obj P.x
      x := P.x
      y := sourceLiftObject (γ := γ) J P
      hx := rfl
      hy := familyBase J p hJ P.x
      iso := replaceSourceIso B S hS d 𝒳' 𝒳 𝒴 F' F G γ (J.obj P.x) P.y P.iso
        (sourceLift_vertical J P)
      vertical := by
        refine IsHomLift.of_fac' _ _ _ (familyBase J p hJ P.x) (familyBase J p hJ P.x) ?_
        change (𝟙 (J.obj P.x).U) = _
        simp [finiteHilbertProjection] }
  map {P Q} φ :=
    { hbase := p.map φ.a
      a := φ.a
      b := sourceLiftMap (γ := γ) J φ
      ha := IsHomLift.map _ _
      hb := by
        refine IsHomLift.of_fac' _ _ _ (familyBase J p hJ P.x) (familyBase J p hJ Q.x) ?_
        exact Functor.congr_hom hJ φ.a
      w := by
        refine FiniteHilbert.Hom.ext ?_ ?_ ?_ φ.w <;>
          exact (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id P := by
    refine TwoFibreProductOver.Hom.ext (p.map_id _) rfl ?_
    exact (sourceLiftFunctor (γ := γ) J).map_id P
  map_comp φ ψ := by
    refine TwoFibreProductOver.Hom.ext (p.map_comp _ _) rfl ?_
    exact (sourceLiftFunctor (γ := γ) J).map_comp φ ψ

attribute [local implicit_reducible] sourceLiftMap sourceLiftFunctor sourceLiftToHilbertLift

/-- The comparison 1-morphism `AlgebraicGeometry.Stack.sourceLiftToHilbertLift` is faithful. -/
private theorem sourceLiftToHilbertLift_faithful :
    (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).Faithful where
  map_injective h :=
    TwoFibreProductOver.Hom.ext' (congrArg (fun f => f.a) h) (congrArg (fun f => f.b.a) h)

/-- The three components of a morphism of `AlgebraicGeometry.Stack.HilbertLift` between two
objects in the image of the comparison 1-morphism which do not involve `𝒳'` are the components of
the morphism of the family. -/
private theorem hilbertLiftHom_components {P Q : SourceLift (G := G) J}
    (φ : (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).obj P ⟶
      (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).obj Q) :
    φ.b.f = (J.map φ.a).f ∧ φ.b.g = (J.map φ.a).g ∧ φ.b.b = (J.map φ.a).b := by
  exact ⟨(Category.id_comp _).symm.trans ((congrArg (·.f) φ.w).symm.trans (Category.comp_id _)),
    (Category.id_comp _).symm.trans ((congrArg (·.g) φ.w).symm.trans (Category.comp_id _)),
    (Category.id_comp _).symm.trans ((congrArg (·.b) φ.w).symm.trans (Category.comp_id _))⟩

/-- The preimage under the comparison 1-morphism of a morphism of
`AlgebraicGeometry.Stack.HilbertLift` between two objects in its image. -/
private def sourceLiftHomPreimage {P Q : SourceLift (G := G) J}
    (φ : (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).obj P ⟶
      (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).obj Q) : P ⟶ Q :=
  TwoFibreProductOver.Hom.mk' φ.a φ.b.a
    (by
      have h := φ.b.a_over
      rw [IsHomLift.fac' _ φ.b.g φ.b.a]
      change eqToHom P.hy.symm ≫ (eqToHom (sourceLiftObject (γ := γ) J P).x_over ≫ φ.b.g ≫
        eqToHom (sourceLiftObject (γ := γ) J Q).x_over.symm) ≫ eqToHom Q.hy = _
      rw [(hilbertLiftHom_components J p hJ φ).2.1]
      simp [finiteHilbertCover])
    (congrArg (fun f => f.a) φ.w)

/-- The comparison 1-morphism `AlgebraicGeometry.Stack.sourceLiftToHilbertLift` is full. -/
private theorem sourceLiftToHilbertLift_full :
    (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ).Full where
  map_surjective {P Q} φ := by
    refine ⟨sourceLiftHomPreimage J p hJ φ, ?_⟩
    refine TwoFibreProductOver.Hom.ext' rfl ?_
    exact FiniteHilbert.Hom.ext (hilbertLiftHom_components J p hJ φ).1.symm
      (hilbertLiftHom_components J p hJ φ).2.1.symm
      (hilbertLiftHom_components J p hJ φ).2.2.symm rfl

/-- The projection of `AlgebraicGeometry.Stack.SourceLift` to the indexing category. -/
private abbrev sourceLiftProjection : SourceLift (G := G) J ⥤ D :=
  TwoFibreProductOver.fst _ _ _ _ _

/-- The projection of `AlgebraicGeometry.Stack.HilbertLift` to the indexing category. -/
private abbrev hilbertLiftProjection : HilbertLift (F' := F') (γ := γ) J p ⥤ D :=
  TwoFibreProductOver.fst _ _ _ _ _

/-- Every object of `AlgebraicGeometry.Stack.HilbertLift` is vertically isomorphic to one in the
image of the comparison 1-morphism. -/
private theorem sourceLiftToHilbertLift_verticalPreimages :
    Functor.HasVerticalPreimages (sourceLiftProjection (G := G) J)
      (hilbertLiftProjection (γ := γ) J p)
      (sourceLiftToHilbertLift (F' := F') (γ := γ) J p hJ) := by
  intro R
  let eZ : (J.obj R.x).Z ≅ R.y.Z := (finiteHilbertCover B S hS d 𝒳 𝒴 F).mapIso R.iso
  let eX : (J.obj R.x).x ≅ G.obj R.y.x := (finiteHilbertSource B S hS d 𝒳 𝒴 F).mapIso R.iso
  have hp := 𝒳'.isStackInGroupoids.isFiberedInGroupoids
  obtain ⟨x', a, ha⟩ := hp.exists_lift eZ.hom R.y.x R.y.x_over
  have hcart := hp.isStronglyCartesian_homLift eZ.hom a
  have hai : IsIso a :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳'.toBasedCategory.p eZ.hom a
  let i := eX ≪≫ (G.toFunctor.mapIso (asIso a)).symm
  have hi : 𝒳.toBasedCategory.p.IsHomLift (𝟙 (J.obj R.x).Z) i.hom := by
    have hax : 𝒳.toBasedCategory.p.IsHomLift eZ.hom eX.hom := R.iso.hom.a_over
    have hGa : 𝒳.toBasedCategory.p.IsHomLift eZ.hom (G.toFunctor.mapIso (asIso a)).hom :=
      BasedFunctor.preserves_isHomLift G eZ.hom a
    have hGai := IsHomLift.inv_lift_inv 𝒳.toBasedCategory.p eZ (G.toFunctor.mapIso (asIso a))
    have hc := IsHomLift.comp 𝒳.toBasedCategory.p eZ.hom eZ.inv eX.hom
      (G.toFunctor.mapIso (asIso a)).inv
    simpa only [i, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id] using hc
  let P : SourceLift (G := G) J :=
    { base := (J.obj R.x).Z
      x := R.x
      y := x'
      hx := rfl
      hy := IsHomLift.domain_eq _ eZ.hom a
      iso := i
      vertical := hi }
  have hc : F.map eX.hom ≫ squareComparisonId γ R.y.x ≫ R.y.α =
      (J.obj R.x).α ≫ R.iso.hom.b := R.iso.hom.compatible
  have hiv : F.map i.inv = F.map (G.map a) ≫ F.map eX.inv := by
    rw [← F.map_comp]
    rfl
  have hxi : F.map eX.inv ≫ F.map eX.hom = 𝟙 (F.obj (G.obj R.y.x)) := by
    rw [← F.map_comp, eX.inv_hom_id, F.map_id]
  let b : sourceLiftObject (γ := γ) J P ⟶ R.y :=
    { f := R.iso.hom.f
      g := R.iso.hom.g
      square := R.iso.hom.square
      b := R.iso.hom.b
      b_over := R.iso.hom.b_over
      a := a
      a_over := ha
      compatible := (show F'.map a ≫ R.y.α =
          (squareComparisonIdInv γ x' ≫ F.map i.inv ≫ (J.obj R.x).α) ≫ R.iso.hom.b from
        calc F'.map a ≫ R.y.α
            = F'.map a ≫ squareComparisonIdInv γ R.y.x ≫ squareComparisonId γ R.y.x ≫ R.y.α := by
              rw [← Category.assoc (squareComparisonIdInv γ R.y.x), squareComparisonIdInv_comp,
                Category.id_comp]
          _ = squareComparisonIdInv γ x' ≫ F.map (G.map a) ≫
                squareComparisonId γ R.y.x ≫ R.y.α := by
              rw [← Category.assoc, squareComparisonIdInv_naturality γ a, Category.assoc]
          _ = squareComparisonIdInv γ x' ≫ F.map (G.map a) ≫ F.map eX.inv ≫ F.map eX.hom ≫
                squareComparisonId γ R.y.x ≫ R.y.α := by
              rw [← Category.assoc (F.map eX.inv), hxi, Category.id_comp]
          _ = squareComparisonIdInv γ x' ≫ F.map i.inv ≫ F.map eX.hom ≫
                squareComparisonId γ R.y.x ≫ R.y.α := by
              rw [hiv, Category.assoc]
          _ = (squareComparisonIdInv γ x' ≫ F.map i.inv ≫ (J.obj R.x).α) ≫ R.iso.hom.b := by
              simp only [Category.assoc]
              rw [← hc]) }
  let t : (sourceLiftToHilbertLift (γ := γ) J p hJ).obj P ⟶ R :=
    TwoFibreProductOver.Hom.mk' (𝟙 R.x) b
      (by
        have hv := R.vertical
        have hf := IsHomLift.fac' (finiteHilbertProjection (B := B) (S := S) (hS := hS)
          (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (𝟙 R.base) R.iso.hom
        change R.iso.hom.f = eqToHom ((familyBase J p hJ R.x).trans R.hx) ≫ 𝟙 R.base ≫
          eqToHom R.hy.symm at hf
        change eqToHom (familyBase J p hJ R.x).symm ≫ R.iso.hom.f ≫ eqToHom R.hy =
          eqToHom rfl ≫ p.map (𝟙 R.x) ≫ eqToHom R.hx
        rw [hf, p.map_id]
        simp)
      (by
        refine FiniteHilbert.Hom.ext (congrArg (·.f ≫ R.iso.hom.f) (J.map_id R.x))
          (congrArg (·.g ≫ R.iso.hom.g) (J.map_id R.x))
          (congrArg (·.b ≫ R.iso.hom.b) (J.map_id R.x)) ?_
        change (J.map (𝟙 R.x)).a ≫ eX.hom = i.hom ≫ G.map a
        rw [J.map_id]
        change (𝟙 (J.obj R.x).x) ≫ eX.hom = i.hom ≫ G.map a
        simp [i])
  have hfiso : IsIso R.iso.hom.f :=
    inferInstanceAs (IsIso ((finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).mapIso R.iso).hom)
  have hblift : (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F') (d := d)).IsHomLift R.iso.hom.f b :=
    IsHomLift.map _ b
  have hbc := (isFiberedInGroupoids_finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F') (d := d)).isStronglyCartesian_homLift R.iso.hom.f b
  have hbi : IsIso b := Functor.IsStronglyCartesian.isIso_of_base_isIso
    (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F') (d := d)) R.iso.hom.f b
  have hta : IsIso t.a := by
    change IsIso (𝟙 R.x)
    infer_instance
  have htb : IsIso t.b := hbi
  have htbase : IsIso t.hbase := by
    have ht := t.ha
    exact IsHomLift.isIso_of_lift_isIso p t.hbase t.a
  have hti : IsIso t := isIso_twoFibreProductOver_hom t
  have ht : (hilbertLiftProjection (γ := γ) J p).IsHomLift (𝟙 R.x) t := IsHomLift.map _ t
  have ht' : (hilbertLiftProjection (γ := γ) J p).IsHomLift (𝟙 R.x) (asIso t).hom := ht
  exact ⟨P, rfl, (asIso t).symm,
    IsHomLift.lift_id_inv (hilbertLiftProjection (γ := γ) J p) R.x (asIso t)⟩

/-- The fibre of the induced 1-morphism of relative finite Hilbert categories along a family is the
2-fibre product of the family with `𝒳'` over `𝒳`, as an equivalence over the indexing category. -/
private noncomputable def sourceLiftEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (sourceLiftProjection (G := G) J)
      (hilbertLiftProjection (F' := F') (γ := γ) J p) := by
  have := sourceLiftToHilbertLift_faithful (γ := γ) J p hJ
  have := sourceLiftToHilbertLift_full (γ := γ) J p hJ
  exact equivalenceOverOfVerticalPreimages (sourceLiftToHilbertLift (γ := γ) J p hJ) rfl
    (sourceLiftToHilbertLift_verticalPreimages (γ := γ) J p hJ)

end HilbertMap

/-! ### The universal family over the base of an object -/

section HilbertFamily

attribute [local implicit_reducible] BasedFunctor.comp BasedFunctor.id BasedCategory.ofFunctor
  finiteHilbertCategory finiteHilbertProjection squareComparison mapRelativeFunctor mapRelative
  finiteHilbertSource finiteHilbertCover CategoryTheory.Functor.Fiber
  CategoryTheory.Over.iteratedSliceBackward CategoryTheory.Over.homMk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳' 𝒳 𝒴 : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory}
  (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d)

/-- The scheme-valued point of `ℋ_d(𝒳/𝒴)` over the base `U` of an object
`ξ = (U, Z, y, x, α)`: the 1-morphism `(Sch/U)_fppf ⟶ ℋ_d(𝒳/𝒴)` which the 2-Yoneda lemma attaches
to `ξ`, assembled from chosen strongly cartesian lifts of the structure morphisms of the
slice. -/
noncomputable def FiniteHilbert.Object.universalFamily :
    Over ξ.U.left ⥤ FiniteHilbert.Object B S hS 𝒳 𝒴 F d :=
  Over.iteratedSliceBackward ξ.U ⋙
    Functor.TwoYoneda.liftFunctor finiteHilbertProjection
      isFiberedInGroupoids_finiteHilbertProjection ξ.U (Functor.Fiber.mk rfl)

/-- The universal family of an object of `ℋ_d(𝒳/𝒴)` is a 1-morphism over the big fppf site: it
sends `T / U` to an object over the image of `T` in the site of `S`. -/
theorem FiniteHilbert.Object.universalFamily_comp :
    ξ.universalFamily ⋙ finiteHilbertProjection = Over.map ξ.U.hom := by
  dsimp only [FiniteHilbert.Object.universalFamily]
  rw [Functor.assoc, Functor.TwoYoneda.liftFunctor_w]
  rfl

/-- The scheme-valued point of `𝒳` over the cover `Z` of an object `ξ = (U, Z, y, x, α)` of
`ℋ_d(𝒳/𝒴)`: the 1-morphism `(Sch/Z)_fppf ⟶ 𝒳` which the 2-Yoneda lemma attaches to `x`. -/
noncomputable def FiniteHilbert.Object.sourcePoint : Over ξ.Z.left ⥤ 𝒳.toBasedCategory.obj :=
  Over.iteratedSliceBackward ξ.Z ⋙
    Functor.TwoYoneda.liftFunctor 𝒳.toBasedCategory.p
      𝒳.isStackInGroupoids.isFiberedInGroupoids ξ.Z (Functor.Fiber.mk ξ.x_over)

/-- The scheme-valued point of `𝒳` attached to an object of `ℋ_d(𝒳/𝒴)` is a 1-morphism over the
big fppf site. -/
theorem FiniteHilbert.Object.sourcePoint_comp :
    ξ.sourcePoint ⋙ 𝒳.toBasedCategory.p = Over.map ξ.Z.hom := by
  dsimp only [FiniteHilbert.Object.sourcePoint]
  rw [Functor.assoc, Functor.TwoYoneda.liftFunctor_w]
  rfl

/-- The chosen strongly cartesian lift of the structure morphism of a test object out of which
the universal family of an object of `ℋ_d(𝒳/𝒴)` is assembled. -/
private noncomputable abbrev universalFamilyLift (T : Over ξ.U.left) :=
  Functor.TwoYoneda.chosenLift finiteHilbertProjection
    isFiberedInGroupoids_finiteHilbertProjection ξ.U (Functor.Fiber.mk (a := ξ) rfl)
    ((Over.iteratedSliceBackward ξ.U).obj T)

/-- The chosen strongly cartesian morphism from a member of the universal family to the object
it is the family of. -/
private noncomputable def universalFamilyArrow (T : Over ξ.U.left) :
    ξ.universalFamily.obj T ⟶ ξ :=
  (universalFamilyLift ξ T).φ

attribute [local implicit_reducible] FiniteHilbert.Object.universalFamily universalFamilyArrow
  FiniteHilbert.Object.sourcePoint

/-- The chosen morphism out of a member of the universal family is strongly cartesian over the
structure morphism of the test object. -/
private theorem universalFamilyArrow_isStronglyCartesianBase (T : Over ξ.U.left) :
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsStronglyCartesian ((Over.iteratedSliceBackward ξ.U).obj T).hom
      (universalFamilyArrow ξ T) :=
  (universalFamilyLift ξ T).isStronglyCartesian

/-- The chosen morphism out of a member of the universal family lies over the structure morphism
of the test object. -/
private theorem universalFamilyArrow_over (T : Over ξ.U.left) :
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsHomLift ((Over.iteratedSliceBackward ξ.U).obj T).hom
      (universalFamilyArrow ξ T) :=
  (universalFamilyArrow_isStronglyCartesianBase ξ T).toIsHomLift

/-- The chosen morphisms out of the universal family are compatible with its transition
morphisms. -/
private theorem universalFamilyArrow_naturality {T T' : Over ξ.U.left} (f : T ⟶ T') :
    ξ.universalFamily.map f ≫ universalFamilyArrow ξ T' = universalFamilyArrow ξ T :=
  have _h := universalFamilyArrow_isStronglyCartesianBase ξ T'
  have _h' := universalFamilyArrow_over ξ T
  Functor.IsStronglyCartesian.fac finiteHilbertProjection
    ((Over.iteratedSliceBackward ξ.U).obj T').hom (universalFamilyArrow ξ T')
    (Over.w ((Over.iteratedSliceBackward ξ.U).map f)).symm (universalFamilyArrow ξ T)

/-- The base object of a member of the universal family is the image of the test object. -/
private theorem universalFamily_base_obj (T : Over ξ.U.left) :
    (ξ.universalFamily.obj T).U = (Over.map ξ.U.hom).obj T :=
  congrArg (fun K => K.obj T) (FiniteHilbert.Object.universalFamily_comp ξ)

/-- The base component of the chosen morphism out of a member of the universal family is the
structure morphism of the test object. -/
private theorem universalFamilyArrow_base (T : Over ξ.U.left) :
    (universalFamilyArrow ξ T).f = eqToHom (universalFamily_base_obj ξ T) ≫
      ((Over.iteratedSliceBackward ξ.U).obj T).hom := by
  have h := universalFamilyArrow_over ξ T
  have hf : (universalFamilyArrow ξ T).f = eqToHom (universalFamily_base_obj ξ T) ≫
      ((Over.iteratedSliceBackward ξ.U).obj T).hom ≫ eqToHom rfl :=
    IsHomLift.fac' (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := d)) ((Over.iteratedSliceBackward ξ.U).obj T).hom (universalFamilyArrow ξ T)
  simpa only [eqToHom_refl, Category.comp_id] using hf

/-- The family of covers underlying the universal family, as a family of test objects over the
cover `Z`: a test object `T / U` is sent to the cover of the member of the universal family at
`T`, regarded over `Z` through the chosen morphism. -/
private noncomputable def familyCover : Over ξ.U.left ⥤ Over ξ.Z.left where
  obj T := Over.mk (universalFamilyArrow ξ T).g.left
  map f := Over.homMk (ξ.universalFamily.map f).g.left
    (congrArg (fun g => g.g.left) (universalFamilyArrow_naturality ξ f))
  map_id T := Over.OverMorphism.ext (congrArg (·.g.left) (ξ.universalFamily.map_id T))
  map_comp f g := Over.OverMorphism.ext (congrArg (·.g.left) (ξ.universalFamily.map_comp f g))

attribute [local implicit_reducible] familyCover

/-- The image in the site of `S` of a member of the family of covers is the cover of the
corresponding member of the universal family. -/
private theorem familyCover_base_obj (T : Over ξ.U.left) :
    (Over.map ξ.Z.hom).obj ((familyCover ξ).obj T) = (ξ.universalFamily.obj T).Z := by
  change Over.mk ((universalFamilyArrow ξ T).g.left ≫ ξ.Z.hom) = _
  rw [(universalFamilyArrow ξ T).g.w]
  rfl

/-- The family of covers is the family of covers of the universal family. -/
private theorem familyCover_base :
    familyCover ξ ⋙ Over.map ξ.Z.hom =
      ξ.universalFamily ⋙ finiteHilbertCover B S hS d 𝒳 𝒴 F := by
  refine CategoryTheory.Functor.ext (familyCover_base_obj ξ) ?_
  intro T T' f
  refine Over.OverMorphism.ext ?_
  simp
  rfl

/-- The chosen strongly cartesian lift of the structure morphism of a test object out of which
the scheme-valued point of `𝒳` attached to an object of `ℋ_d(𝒳/𝒴)` is assembled. -/
private noncomputable abbrev sourcePointLift (A : Over ξ.Z.left) :=
  Functor.TwoYoneda.chosenLift 𝒳.toBasedCategory.p
    𝒳.isStackInGroupoids.isFiberedInGroupoids ξ.Z (Functor.Fiber.mk ξ.x_over)
    ((Over.iteratedSliceBackward ξ.Z).obj A)

/-- The chosen strongly cartesian morphism from a member of the scheme-valued point of `𝒳` to the
object `x`. -/
private noncomputable def sourcePointArrow (A : Over ξ.Z.left) :
    ξ.sourcePoint.obj A ⟶ ξ.x :=
  (sourcePointLift ξ A).φ

attribute [local implicit_reducible] sourcePointArrow

/-- The chosen morphism out of a member of the scheme-valued point of `𝒳` is strongly cartesian
over the structure morphism of the test object. -/
private theorem sourcePointArrow_isStronglyCartesian (A : Over ξ.Z.left) :
    𝒳.toBasedCategory.p.IsStronglyCartesian ((Over.iteratedSliceBackward ξ.Z).obj A).hom
      (sourcePointArrow ξ A) :=
  (sourcePointLift ξ A).isStronglyCartesian

/-- The chosen morphism out of a member of the scheme-valued point of `𝒳` lies over the structure
morphism of the test object. -/
private theorem sourcePointArrow_over (A : Over ξ.Z.left) :
    𝒳.toBasedCategory.p.IsHomLift ((Over.iteratedSliceBackward ξ.Z).obj A).hom
      (sourcePointArrow ξ A) :=
  (sourcePointArrow_isStronglyCartesian ξ A).toIsHomLift

/-- The chosen morphisms out of the scheme-valued point of `𝒳` are compatible with its transition
morphisms. -/
private theorem sourcePointArrow_naturality {A A' : Over ξ.Z.left} (f : A ⟶ A') :
    ξ.sourcePoint.map f ≫ sourcePointArrow ξ A' = sourcePointArrow ξ A :=
  have _h := sourcePointArrow_isStronglyCartesian ξ A'
  have _h' := sourcePointArrow_over ξ A
  Functor.IsStronglyCartesian.fac 𝒳.toBasedCategory.p
    ((Over.iteratedSliceBackward ξ.Z).obj A').hom (sourcePointArrow ξ A')
    (Over.w ((Over.iteratedSliceBackward ξ.Z).map f)).symm (sourcePointArrow ξ A)

/-- The cover component of the chosen morphism out of a member of the universal family is the
structure morphism of the corresponding member of the family of covers. -/
private theorem familyCover_arrow (T : Over ξ.U.left) :
    (universalFamilyArrow ξ T).g = eqToHom (familyCover_base_obj ξ T).symm ≫
      ((Over.iteratedSliceBackward ξ.Z).obj ((familyCover ξ).obj T)).hom := by
  refine Over.OverMorphism.ext ?_
  change (universalFamilyArrow ξ T).g.left =
    (eqToHom (familyCover_base_obj ξ T).symm).left ≫ (universalFamilyArrow ξ T).g.left
  simp

/-- The object-of-`𝒳` component of the chosen morphism out of a member of the universal family is
strongly cartesian. -/
private theorem universalFamilyArrow_isStronglyCartesian (T : Over ξ.U.left) :
    𝒳.toBasedCategory.p.IsStronglyCartesian (universalFamilyArrow ξ T).g
      (universalFamilyArrow ξ T).a := by
  have h : 𝒳.toBasedCategory.p.IsHomLift (universalFamilyArrow ξ T).g
      (universalFamilyArrow ξ T).a := (universalFamilyArrow ξ T).a_over
  exact 𝒳.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift
    (universalFamilyArrow ξ T).g (universalFamilyArrow ξ T).a

/-- The object of `𝒳` carried by a member of the universal family is the member of the
scheme-valued point of `𝒳` at the corresponding test object over `Z`. -/
private noncomputable def familySourceIso (T : Over ξ.U.left) :
    (ξ.universalFamily.obj T).x ≅ ξ.sourcePoint.obj ((familyCover ξ).obj T) := by
  have h₁ := sourcePointArrow_isStronglyCartesian ξ ((familyCover ξ).obj T)
  have h₂ := universalFamilyArrow_isStronglyCartesian ξ T
  exact Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒳.toBasedCategory.p
    (g := eqToIso (familyCover_base_obj ξ T).symm) (familyCover_arrow ξ T)
    (sourcePointArrow ξ ((familyCover ξ).obj T)) (universalFamilyArrow ξ T).a

/-- The identification of `AlgebraicGeometry.Stack.familySourceIso` is vertical. -/
private theorem familySourceIso_over (T : Over ξ.U.left) :
    𝒳.toBasedCategory.p.IsHomLift (𝟙 ((Over.map ξ.Z.hom).obj ((familyCover ξ).obj T)))
      (familySourceIso ξ T).hom := by
  have h₁ := sourcePointArrow_isStronglyCartesian ξ ((familyCover ξ).obj T)
  have h₂ := universalFamilyArrow_isStronglyCartesian ξ T
  have h : 𝒳.toBasedCategory.p.IsHomLift (eqToHom (familyCover_base_obj ξ T).symm)
      (familySourceIso ξ T).hom :=
    Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift 𝒳.toBasedCategory.p
      (g := eqToIso (familyCover_base_obj ξ T).symm) (familyCover_arrow ξ T)
      (sourcePointArrow ξ ((familyCover ξ).obj T)) (universalFamilyArrow ξ T).a
  have hd := IsHomLift.domain_eq 𝒳.toBasedCategory.p
    (eqToHom (familyCover_base_obj ξ T).symm) (familySourceIso ξ T).hom
  have hc := IsHomLift.codomain_eq 𝒳.toBasedCategory.p
    (eqToHom (familyCover_base_obj ξ T).symm) (familySourceIso ξ T).hom
  refine IsHomLift.of_fac' _ _ _ (hd.trans (familyCover_base_obj ξ T).symm) hc ?_
  rw [IsHomLift.fac' _ (eqToHom (familyCover_base_obj ξ T).symm) (familySourceIso ξ T).hom]
  simp

/-- The identification of `AlgebraicGeometry.Stack.familySourceIso` is compatible with the chosen
morphisms to `x`. -/
private theorem familySourceIso_fac (T : Over ξ.U.left) :
    (familySourceIso ξ T).hom ≫ sourcePointArrow ξ ((familyCover ξ).obj T) =
      (universalFamilyArrow ξ T).a := by
  have h₁ := sourcePointArrow_isStronglyCartesian ξ ((familyCover ξ).obj T)
  have h₂ := universalFamilyArrow_isStronglyCartesian ξ T
  have h₃ := h₂.toIsHomLift
  dsimp only [familySourceIso, Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac 𝒳.toBasedCategory.p
    ((Over.iteratedSliceBackward ξ.Z).obj ((familyCover ξ).obj T)).hom
    (sourcePointArrow ξ ((familyCover ξ).obj T)) (familyCover_arrow ξ T)
    (universalFamilyArrow ξ T).a

/-- The objects of `𝒳` carried by the universal family are the scheme-valued point of `𝒳` reindexed
along the family of covers, with components `AlgebraicGeometry.Stack.familySourceIso`. -/
private noncomputable def familySourceNatIso :
    ξ.universalFamily ⋙ finiteHilbertSource B S hS d 𝒳 𝒴 F ≅ familyCover ξ ⋙ ξ.sourcePoint :=
  NatIso.ofComponents (familySourceIso ξ) (by
    intro T T' f
    change (ξ.universalFamily.map f).a ≫ (familySourceIso ξ T').hom =
      (familySourceIso ξ T).hom ≫ ξ.sourcePoint.map ((familyCover ξ).map f)
    have hsc : 𝒳.toBasedCategory.p.IsStronglyCartesian
        ((Over.iteratedSliceBackward ξ.Z).obj ((familyCover ξ).obj T')).hom
        (sourcePointArrow ξ ((familyCover ξ).obj T')) :=
      sourcePointArrow_isStronglyCartesian ξ ((familyCover ξ).obj T')
    have hi : 𝒳.toBasedCategory.p.IsHomLift
        (𝟙 ((Over.map ξ.Z.hom).obj ((familyCover ξ).obj T))) (familySourceIso ξ T).hom :=
      familySourceIso_over ξ T
    have hi' : 𝒳.toBasedCategory.p.IsHomLift
        (𝟙 ((Over.map ξ.Z.hom).obj ((familyCover ξ).obj T'))) (familySourceIso ξ T').hom :=
      familySourceIso_over ξ T'
    have hr : 𝒳.toBasedCategory.p.IsHomLift ((Over.map ξ.Z.hom).map ((familyCover ξ).map f))
        (ξ.sourcePoint.map ((familyCover ξ).map f)) :=
      Functor.isHomLift_map_of_comp_eq (FiniteHilbert.Object.sourcePoint_comp ξ) _ _
    have ha : 𝒳.toBasedCategory.p.IsHomLift (ξ.universalFamily.map f).g
        (ξ.universalFamily.map f).a := (ξ.universalFamily.map f).a_over
    have hl' : 𝒳.toBasedCategory.p.IsHomLift ((Over.map ξ.Z.hom).map ((familyCover ξ).map f))
        (ξ.universalFamily.map f).a := by
      refine IsHomLift.of_fac' _ _ _
        ((ξ.universalFamily.obj T).x_over.trans (familyCover_base_obj ξ T).symm)
        ((ξ.universalFamily.obj T').x_over.trans (familyCover_base_obj ξ T').symm) ?_
      rw [IsHomLift.fac' _ (ξ.universalFamily.map f).g (ξ.universalFamily.map f).a]
      have h : (Over.map ξ.Z.hom).map ((familyCover ξ).map f) =
          eqToHom (familyCover_base_obj ξ T) ≫ (ξ.universalFamily.map f).g ≫
            eqToHom (familyCover_base_obj ξ T').symm :=
        CategoryTheory.Functor.congr_hom (familyCover_base ξ) f
      rw [h]
      simp
    have hh₁ : 𝒳.toBasedCategory.p.IsHomLift ((Over.map ξ.Z.hom).map ((familyCover ξ).map f))
        ((ξ.universalFamily.map f).a ≫ (familySourceIso ξ T').hom) :=
      IsHomLift.comp_lift_id_right 𝒳.toBasedCategory.p _ _ _
    have hh₂ : 𝒳.toBasedCategory.p.IsHomLift ((Over.map ξ.Z.hom).map ((familyCover ξ).map f))
        ((familySourceIso ξ T).hom ≫ ξ.sourcePoint.map ((familyCover ξ).map f)) :=
      IsHomLift.comp_lift_id_left 𝒳.toBasedCategory.p _ _ _
    refine Functor.IsStronglyCartesian.ext 𝒳.toBasedCategory.p
      ((Over.iteratedSliceBackward ξ.Z).obj ((familyCover ξ).obj T')).hom
      (sourcePointArrow ξ ((familyCover ξ).obj T'))
      ((Over.map ξ.Z.hom).map ((familyCover ξ).map f)) ?_
    rw [Category.assoc, familySourceIso_fac, Category.assoc, sourcePointArrow_naturality,
      familySourceIso_fac]
    exact congrArg (fun g => g.a) (universalFamilyArrow_naturality ξ f))

/-- The cover of a member of the universal family presents the fibre product of the test object
with `Z` over `U`. -/
private theorem familyProduct_isPullback (T : Over ξ.U.left) :
    IsPullback (universalFamilyArrow ξ T).g.left
      ((ξ.universalFamily.obj T).q.left ≫
        eqToHom (congrArg Over.left (universalFamily_base_obj ξ T)))
      ξ.q.left T.hom := by
  have h := (universalFamilyArrow ξ T).square.map (Over.forget _)
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (eqToIso (congrArg Over.left (universalFamily_base_obj ξ T))) (Iso.refl _) (by simp)
    (by simp) (by simp) ?_
  have hf := congrArg (fun f => f.left) (universalFamilyArrow_base ξ T)
  change (universalFamilyArrow ξ T).f.left =
    (eqToHom (universalFamily_base_obj ξ T)).left ≫ T.hom at hf
  change (universalFamilyArrow ξ T).f.left ≫ 𝟙 ξ.U.left =
    eqToHom (congrArg Over.left (universalFamily_base_obj ξ T)) ≫ T.hom
  simpa only [Over.eqToHom_left, Category.comp_id] using hf

/-- The fibre product `T ×_U Z`, as a test object over `U`. -/
private noncomputable def familyProduct (T : Over ξ.U.left) : Over ξ.U.left :=
  Over.mk ((universalFamilyArrow ξ T).g.left ≫ ξ.q.left)

/-- The first projection of `AlgebraicGeometry.Stack.familyProduct`. -/
private noncomputable def familyProductFst (T : Over ξ.U.left) : familyProduct ξ T ⟶ T :=
  Over.homMk ((ξ.universalFamily.obj T).q.left ≫
    eqToHom (congrArg Over.left (universalFamily_base_obj ξ T)))
    (familyProduct_isPullback ξ T).w.symm

/-- The second projection of `AlgebraicGeometry.Stack.familyProduct`. -/
private noncomputable def familyProductSnd (T : Over ξ.U.left) :
    familyProduct ξ T ⟶ Over.mk ξ.q.left :=
  Over.homMk (universalFamilyArrow ξ T).g.left rfl

attribute [local implicit_reducible] familyProduct familyProductFst familyProductSnd

/-- `AlgebraicGeometry.Stack.familyProduct` is the binary product of `T` and `Z` in the slice over
`U`. -/
private noncomputable def familyProductLimit (T : Over ξ.U.left) :
    IsLimit (BinaryFan.mk (familyProductFst ξ T) (familyProductSnd ξ T)) :=
  overBinaryFanIsLimit ξ.q.left T (familyProduct ξ T) (familyProductFst ξ T)
    (familyProductSnd ξ T) (familyProduct_isPullback ξ T)

/-- The presheaf represented by `AlgebraicGeometry.Stack.familyProduct` is the product of the two
representable presheaves. -/
private noncomputable def familyProductIso (T : Over ξ.U.left) :
    yoneda.obj (familyProduct ξ T) ≅ yoneda.obj T ⨯ yoneda.obj (Over.mk ξ.q.left) :=
  yonedaBinaryProductIso (familyProductFst ξ T) (familyProductSnd ξ T) (familyProductLimit ξ T)

/-- The first projection of `AlgebraicGeometry.Stack.familyProductIso`. -/
private theorem familyProductIso_fst (T : Over ξ.U.left) :
    (familyProductIso ξ T).hom ≫ prod.fst = yoneda.map (familyProductFst ξ T) :=
  yonedaBinaryProductIso_fst _ _ _

/-- The second projection of `AlgebraicGeometry.Stack.familyProductIso`. -/
private theorem familyProductIso_snd (T : Over ξ.U.left) :
    (familyProductIso ξ T).hom ≫ prod.snd = yoneda.map (familyProductSnd ξ T) :=
  yonedaBinaryProductIso_snd _ _ _

/-- The transition morphism of the family of fibre products. -/
private noncomputable def familyProductMap {T T' : Over ξ.U.left} (f : T ⟶ T') :
    familyProduct ξ T ⟶ familyProduct ξ T' :=
  Over.homMk (ξ.universalFamily.map f).g.left (by
    have h := congrArg (fun g => g.g.left) (universalFamilyArrow_naturality ξ f)
    change (ξ.universalFamily.map f).g.left ≫
      ((universalFamilyArrow ξ T').g.left ≫ ξ.q.left) =
      (universalFamilyArrow ξ T).g.left ≫ ξ.q.left
    change (ξ.universalFamily.map f).g.left ≫ (universalFamilyArrow ξ T').g.left =
      (universalFamilyArrow ξ T).g.left at h
    rw [← Category.assoc, h])

attribute [local implicit_reducible] familyProductMap

/-- The transition morphisms of the family of fibre products are over `Z`. -/
private theorem familyProductMap_snd {T T' : Over ξ.U.left} (f : T ⟶ T') :
    familyProductMap ξ f ≫ familyProductSnd ξ T' = familyProductSnd ξ T :=
  Over.OverMorphism.ext (congrArg (fun g => g.g.left) (universalFamilyArrow_naturality ξ f))

/-- The transition morphisms of the family of fibre products are compatible with the first
projections. -/
private theorem familyProductMap_fst {T T' : Over ξ.U.left} (f : T ⟶ T') :
    familyProductMap ξ f ≫ familyProductFst ξ T' = familyProductFst ξ T ≫ f := by
  have hf := congrArg (fun f => f.left)
    (CategoryTheory.Functor.congr_hom (FiniteHilbert.Object.universalFamily_comp ξ) f)
  have hs := congrArg (fun f => f.left) (ξ.universalFamily.map f).square.w
  refine Over.OverMorphism.ext ?_
  change (ξ.universalFamily.map f).g.left ≫
      ((ξ.universalFamily.obj T').q.left ≫
        eqToHom (congrArg Over.left (universalFamily_base_obj ξ T'))) =
    ((ξ.universalFamily.obj T).q.left ≫
      eqToHom (congrArg Over.left (universalFamily_base_obj ξ T))) ≫ f.left
  change (ξ.universalFamily.map f).g.left ≫ (ξ.universalFamily.obj T').q.left =
    (ξ.universalFamily.obj T).q.left ≫ (ξ.universalFamily.map f).f.left at hs
  change (ξ.universalFamily.map f).f.left =
    (eqToHom (universalFamily_base_obj ξ T)).left ≫ f.left ≫
      (eqToHom (universalFamily_base_obj ξ T').symm).left at hf
  rw [← Category.assoc, hs, Category.assoc, hf]
  simp

/-- `AlgebraicGeometry.Stack.familyProductIso` is natural in the test object. -/
private theorem familyProductIso_map {T T' : Over ξ.U.left} (f : T ⟶ T') :
    (familyProductIso ξ T).hom ≫ prod.map (yoneda.map f) (𝟙 _) =
      yoneda.map (familyProductMap ξ f) ≫ (familyProductIso ξ T').hom := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, ← Category.assoc, familyProductIso_fst, Category.assoc,
      familyProductIso_fst, ← yoneda.map_comp, ← yoneda.map_comp, familyProductMap_fst]
  · rw [Category.assoc, prod.map_snd, Category.comp_id, familyProductIso_snd, Category.assoc,
      familyProductIso_snd, ← yoneda.map_comp, familyProductMap_snd]

variable (W : (BigFppfOver B (B.inclusion.obj ξ.Z.left) ξ.Z.left.property)ᵒᵖ ⥤ Type u)
  (w : (OverShriek.relocalizePresheafFunctor ξ.q.left).obj W ⟶
    yoneda.obj (Over.mk ξ.q.left : BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property))
  (hw : ∀ (T : BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)
    (s : ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W).obj (op T)),
    (w.app (op T) s).left = s.val.fst)

/-- The sections of the relocalized presheaf over `Z` are the values of the presheaf itself at the
members of the family of covers. -/
private noncomputable def familySectionEquiv (T : Over ξ.U.left) :
    (Space.sectionSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left)
      ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w).obj (op T) ≃
      W.obj (op ((familyCover ξ).obj T)) :=
  (Space.sectionSpaceEquiv B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left) T
    ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w).trans
    (relocalizeSectionsEquiv ξ.q.left W w hw T (familyProduct ξ T) (familyProductSnd ξ T)
      (familyProductIso ξ T) (familyProductIso_snd ξ T))

/-- `AlgebraicGeometry.Stack.familySectionEquiv` is natural in the test object. -/
private theorem familySectionEquiv_map {T T' : Over ξ.U.left} (f : T ⟶ T')
    (s : (Space.sectionSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left)
      ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w).obj (op T')) :
    familySectionEquiv ξ W w hw T
      ((Space.sectionSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left)
        ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w).map f.op s) =
      W.map ((familyCover ξ).map f).op (familySectionEquiv ξ W w hw T' s) := by
  have hs := Space.sectionSpaceEquiv_map B (B.inclusion.obj ξ.U.left) ξ.U.left.property
    (Over.mk ξ.q.left) T' T ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w f s
  have hh := relocalizeSectionsEquiv_map ξ.q.left W w hw f (familyProductMap ξ f)
    (familyProductSnd ξ T') (familyProductSnd ξ T) (familyProductMap_snd ξ f)
    (familyProductIso ξ T') (familyProductIso ξ T) (familyProductIso_snd ξ T')
    (familyProductIso_snd ξ T) (familyProductIso_map ξ f)
    (Space.sectionSpaceEquiv B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left) T'
      ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w s)
  change _ = W.map ((familyCover ξ).map f).op _ at hh
  refine Eq.trans ?_ hh
  exact congrArg (relocalizeSectionsEquiv ξ.q.left W w hw T (familyProduct ξ T)
    (familyProductSnd ξ T) (familyProductIso ξ T) (familyProductIso_snd ξ T)) (Subtype.ext hs)

include hw in
/-- The fibre of the canonical 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over an object
`ξ = (U, Z, y, x, α)` of `ℋ_d(𝒳/𝒴)` is the space of sections over `U` of `W ⟶ Z`, where `W`
represents the fibre of `G : 𝒳' ⟶ 𝒳` over the scheme-valued point `x` of `𝒳` over `Z` (through the
equivalence `hW`), and `w : Λ W ⟶ h_Z` presents the relocalization of `W` over `Z`, with values
identified by `hw`. -/
theorem FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hW : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map ξ.Z.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p
        ξ.sourcePoint G.toFunctor)
      (presheafOfCategories (W ⋙ typeToCat)).p)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map ξ.U.hom)
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
          (d := d)).p
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        ξ.universalFamily
        (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
      (presheafOfCategories (Space.sectionSpace B (B.inclusion.obj ξ.U.left)
        ξ.U.left.property (Over.mk ξ.q.left)
        ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w ⋙ typeToCat)).p) := by
  have e := reindexedSectionEquivalenceOver (familySourceNatIso ξ) (familySourceIso_over ξ)
    hW.some (Space.sectionSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property
      (Over.mk ξ.q.left) ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W) w)
    (familySectionEquiv ξ W w hw) (fun f s => familySectionEquiv_map ξ W w hw f s)
  rw [familyCover_base ξ] at e
  exact ⟨(sourceLiftEquivalenceOver (γ := γ) ξ.universalFamily (Over.map ξ.U.hom)
    (FiniteHilbert.Object.universalFamily_comp ξ)).symm.trans e⟩

end HilbertFamily

end AlgebraicGeometry.Stack

end
