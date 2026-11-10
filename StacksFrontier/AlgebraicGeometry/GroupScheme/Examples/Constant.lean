module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.LocallyConstant.Algebra
public import StacksCore.Tactic.StacksAttribute

/-!
# Constant group schemes

An abstract group `G` determines a group scheme over the terminal scheme by taking one copy of
`Spec ℤ` for every group element; the constant group scheme over an arbitrary base is obtained
from it by base change. The coproduct represents the functor of locally constant `G`-valued
maps, and the functor of points of the constant group scheme over `S` is the group of locally
constant `G`-valued functions on the varying `S`-scheme.

## Main definitions

* `AlgebraicGeometry.constantSchemeOverIntegers` is the coproduct of copies of the terminal
  scheme indexed by a type, and `AlgebraicGeometry.constantSchemeOverIntegersObj` is that
  coproduct regarded as a scheme over the terminal scheme.
* `AlgebraicGeometry.constantComponent` is the inclusion of the component indexed by `g`.
* `AlgebraicGeometry.constantGroupSchemeStructure` equips the coproduct with the group law
  induced by the group law on the indexing type, and
  `AlgebraicGeometry.constantGroupScheme` is its base change to an arbitrary scheme.
* `AlgebraicGeometry.locallyConstantMaps` is the group-valued functor of locally constant maps
  on schemes, `AlgebraicGeometry.locallyConstantMapsOver` its version on schemes over a base,
  and `AlgebraicGeometry.locallyConstantMapsOverIntegers` the latter over the terminal scheme.
* `AlgebraicGeometry.fiberOpen`, `AlgebraicGeometry.fiberCover` and
  `AlgebraicGeometry.ConstantGroupScheme.fiberι` are the gluing data by which a locally constant
  map is turned into a morphism to the coproduct.

## Main results

* `AlgebraicGeometry.constantSchemeOverIntegersPointsIsoLocallyConstantMaps` is the canonical
  isomorphism from the group-valued functor of points of the constant group scheme over the
  terminal scheme to locally constant maps, and
  `AlgebraicGeometry.constantSchemeOverIntegersPointsIsoLocallyConstantMaps_component`
  identifies the image of each component inclusion with the corresponding constant map.
* `AlgebraicGeometry.locallyConstantMaps_representableBy_constantSchemeOverIntegers` records
  representability on the category of schemes.
* `AlgebraicGeometry.constantGroupSchemePointsIsoLocallyConstantMaps` identifies the functor of
  points of the constant group scheme over `S` with locally constant maps.

## Implementation notes

The terminal object of `Scheme` is canonically `Spec ℤ`, so it is used for each component. The
group object over the terminal scheme is specified by requiring its multiplication to carry the
pair of components indexed by `g` and `h` to the component indexed by `g * h`; pullback of group
objects then gives the constant group scheme over the base. The chosen structure is registered
as a `GrpObj` instance on `constantSchemeOverIntegersObj G`, and its component formula is the
second projection of `constantGroupSchemeStructure G`. The component inclusions, their
specification and the base-change construction are abbreviations, so the existing coproduct,
group-object and pullback APIs apply directly.

The group operation on locally constant maps is pointwise, so the natural isomorphisms include
the compatibility of multiplication asserted in the source. Since the indexing group may live in
a larger universe while being small relative to the universe of schemes, the functor of points
is postcomposed with the fully faithful universe-lifting functor on groups; this is only
universe bookkeeping, as the other side consists literally of locally constant `G`-valued maps.
The universe condition `Small.{u} G` is precisely what is needed for the coproduct to be a
scheme in `Scheme.{u}`; any abstract group is allowed by taking a sufficiently large universe.

## References

* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace AlgebraicGeometry

/-- The scheme `G_{Spec ℤ}`, before equipping it with its group structure. -/
@[stacks 03YW "constant_group_scheme_construction"]
abbrev constantSchemeOverIntegers (G : Type v) [Small.{u} G] : Scheme.{u} :=
  ∐ fun _ : G ↦ ⊤_ Scheme.{u}

/-- The coproduct of copies of `Spec ℤ`, regarded as a scheme over `Spec ℤ`. -/
abbrev constantSchemeOverIntegersObj (G : Type v) [Small.{u} G] : Over (⊤_ Scheme.{u}) :=
  Over.mk (terminal.from (constantSchemeOverIntegers G))

/-- The inclusion of the component indexed by `g`, as a morphism over `Spec ℤ`. -/
abbrev constantComponent (G : Type v) [Small.{u} G] (g : G) :
    Over.mk (𝟙 (⊤_ Scheme.{u})) ⟶ constantSchemeOverIntegersObj G :=
  Over.homMk (Sigma.ι (fun _ : G ↦ ⊤_ Scheme.{u}) g)

/-- A group-object structure on the coproduct is the constant one if multiplication on components
is induced by multiplication in the indexing group. -/
abbrev IsConstantGroupSchemeStructure (G : Type v) [Small.{u} G] [Group G]
    (s : GrpObj (constantSchemeOverIntegersObj G)) : Prop :=
  letI := s
  ∀ g h : G,
    lift (constantComponent G g) (constantComponent G h) ≫ MonObj.mul =
      constantComponent G (g * h)

namespace ConstantGroupScheme

/-- The terminal scheme, regarded as a scheme over itself. -/
abbrev unitObj : Over (⊤_ Scheme.{u}) := Over.mk (𝟙 _)

/-- A family of points of an `S`-scheme indexed by `A` describes a morphism out of the
coproduct of copies of the terminal scheme indexed by `A`. -/
def componentDesc {A : Type v} [Small.{u} A] {X : Over (⊤_ Scheme.{u})}
    (f : A → (unitObj ⟶ X)) : constantSchemeOverIntegersObj A ⟶ X :=
  Over.homMk (Sigma.desc fun a ↦ (f a).left) (Subsingleton.elim _ _)

/-- The morphism out of the coproduct determined by a family of points restricts to the point
`f a` on the component indexed by `a`. -/
@[reassoc (attr := simp)]
lemma component_desc {A : Type v} [Small.{u} A] {X : Over (⊤_ Scheme.{u})}
    (f : A → (unitObj ⟶ X)) (a : A) :
    constantComponent A a ≫ componentDesc f = f a :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

/-- Two morphisms out of the coproduct agree as soon as they agree on every component. -/
lemma component_hom_ext {A : Type v} [Small.{u} A] {X : Over (⊤_ Scheme.{u})}
    (f g : constantSchemeOverIntegersObj A ⟶ X)
    (h : ∀ a, constantComponent A a ≫ f = constantComponent A a ≫ g) : f = g :=
  Over.OverMorphism.ext (Sigma.hom_ext _ _ fun a ↦ congrArg Over.Hom.left (h a))

/-- A pair of components is an open immersion into the product of two coproducts. -/
lemma component_pair_open {A B : Type v} [Small.{u} A] [Small.{u} B] (a : A) (b : B) :
    IsOpenImmersion (lift (constantComponent A a) (constantComponent B b)).left := by
  have heq : lift (constantComponent A a) (constantComponent B b) =
      (λ_ unitObj).inv ≫ (constantComponent A a ⊗ₘ constantComponent B b) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [lift_fst, Category.assoc, tensorHom_fst, leftUnitor_inv_fst_assoc]
      change constantComponent A a = toUnit (𝟙_ (Over (⊤_ Scheme.{u}))) ≫ _
      simp
    · simp
  have : IsIso (λ_ unitObj.{u}).inv.left :=
    (Over.forget (⊤_ Scheme.{u})).map_isIso (λ_ unitObj.{u}).inv
  rw [heq, Over.comp_left, Over.tensorHom_left]
  simp only [constantComponent, Over.homMk, CostructuredArrow.homMk_left]
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance (terminal.hom_ext _ _) (terminal.hom_ext _ _))

/-- The components of a product of two coproducts cover it. -/
lemma component_pair_iso {A B : Type v} [Small.{u} A] [Small.{u} B] :
    IsIso (Sigma.desc (f := fun _ : A × B ↦ ⊤_ Scheme.{u}) fun p : A × B ↦
      (lift (constantComponent A p.1) (constantComponent B p.2)).left) := by
  let f : A × B → (⊤_ Scheme.{u} ⟶
      pullback (constantSchemeOverIntegersObj A).hom
        (constantSchemeOverIntegersObj B).hom) := fun p ↦
    (lift (constantComponent A p.1) (constantComponent B p.2)).left
  have (p : A × B) : IsOpenImmersion (f p) := component_pair_open p.1 p.2
  have hfst (p : A × B) : f p ≫ pullback.fst (constantSchemeOverIntegersObj A).hom
      (constantSchemeOverIntegersObj B).hom = Sigma.ι (fun _ : A ↦ ⊤_ Scheme.{u}) p.1 :=
    congrArg Over.Hom.left
      (CartesianMonoidalCategory.lift_fst (constantComponent A p.1) (constantComponent B p.2))
  have hsnd (p : A × B) : f p ≫ pullback.snd (constantSchemeOverIntegersObj A).hom
      (constantSchemeOverIntegersObj B).hom = Sigma.ι (fun _ : B ↦ ⊤_ Scheme.{u}) p.2 :=
    congrArg Over.Hom.left
      (CartesianMonoidalCategory.lift_snd (constantComponent A p.1) (constantComponent B p.2))
  have hdesc : IsOpenImmersion (Sigma.desc f) := by
    apply isOpenImmersion_sigmaDesc
    intro p q hpq
    change Disjoint (Set.range (f p)) (Set.range (f q))
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hxy⟩
    apply hpq
    have h₁ := congrArg (pullback.fst (constantSchemeOverIntegersObj A).hom
      (constantSchemeOverIntegersObj B).hom) hxy
    have h₂ := congrArg (pullback.snd (constantSchemeOverIntegersObj A).hom
      (constantSchemeOverIntegersObj B).hom) hxy
    simp only [← Scheme.Hom.comp_apply, hfst, hsnd] at h₁ h₂
    exact Prod.ext (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp h₁)).symm
      (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp h₂)).symm
  have : IsOpenImmersion (Sigma.desc (f := fun _ : A × B ↦ ⊤_ Scheme.{u})
      fun p : A × B ↦ (lift (constantComponent A p.1) (constantComponent B p.2)).left) := hdesc
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_unique
  intro z _
  let U := Scheme.Pullback.openCoverOfLeftRight
    (sigmaOpenCover (fun _ : A ↦ ⊤_ Scheme.{u}))
    (sigmaOpenCover (fun _ : B ↦ ⊤_ Scheme.{u}))
    (constantSchemeOverIntegersObj A).hom (constantSchemeOverIntegersObj B).hom
  obtain ⟨p, x, hx⟩ := U.exists_eq z
  change A × B at p
  have hfac : U.f p = terminal.from (U.X p) ≫ f p := by
    rw [Scheme.Pullback.openCoverOfLeftRight_f
      (sigmaOpenCover (fun _ : A ↦ ⊤_ Scheme.{u}))
      (sigmaOpenCover (fun _ : B ↦ ⊤_ Scheme.{u}))
      (constantSchemeOverIntegersObj A).hom (constantSchemeOverIntegersObj B).hom p]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        ((congrArg (fun t => t ≫ Sigma.ι (fun _ : A ↦ ⊤_ Scheme.{u}) p.1)
            (terminal.hom_ext _ _)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun t => terminal.from (U.X p) ≫ t) (hfst p))).symm)
    · exact (pullback.lift_snd _ _ _).trans
        ((congrArg (fun t => t ≫ Sigma.ι (fun _ : B ↦ ⊤_ Scheme.{u}) p.2)
            (terminal.hom_ext _ _)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun t => terminal.from (U.X p) ≫ t) (hsnd p))).symm)
  refine ⟨Sigma.ι (fun _ : A × B ↦ ⊤_ Scheme.{u}) p (terminal.from (U.X p) x), ?_⟩
  change (Sigma.desc f) (Sigma.ι (fun _ : A × B ↦ ⊤_ Scheme.{u}) p
    (terminal.from (U.X p) x)) = z
  rw [← Scheme.Hom.comp_apply (Sigma.ι (fun _ : A × B ↦ ⊤_ Scheme.{u}) p)
    (Sigma.desc f), Sigma.ι_comp_desc]
  rw [hfac, Scheme.Hom.comp_apply] at hx
  exact hx

/-- The coproduct indexed by `A × B` is the product of the coproducts indexed by `A` and
by `B`. -/
def componentProductIso (A B : Type v) [Small.{u} A] [Small.{u} B] :
    constantSchemeOverIntegersObj (A × B) ≅
      constantSchemeOverIntegersObj A ⊗ constantSchemeOverIntegersObj B := by
  have := component_pair_iso.{u, v} (A := A) (B := B)
  exact Over.isoMk (asIso (Sigma.desc (f := fun _ : A × B ↦ ⊤_ Scheme.{u}) fun p : A × B ↦
    (lift (constantComponent A p.1) (constantComponent B p.2)).left))
    (Subsingleton.elim _ _)

/-- The isomorphism `componentProductIso A B` sends the component indexed by `(a, b)` to the
pair of components indexed by `a` and by `b`. -/
@[reassoc (attr := simp)]
lemma component_product_hom (A B : Type v) [Small.{u} A] [Small.{u} B] (a : A) (b : B) :
    constantComponent (A × B) (a, b) ≫ (componentProductIso A B).hom =
      lift (constantComponent A a) (constantComponent B b) :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc (fun p : A × B ↦
    (lift (constantComponent A p.1) (constantComponent B p.2)).left) (a, b))

/-- Two morphisms out of a product of coproducts agree as soon as they agree on every pair of
components. -/
lemma pair_hom_ext {A B : Type v} [Small.{u} A] [Small.{u} B] {X : Over (⊤_ Scheme.{u})}
    (f g : constantSchemeOverIntegersObj A ⊗ constantSchemeOverIntegersObj B ⟶ X)
    (h : ∀ a b, lift (constantComponent A a) (constantComponent B b) ≫ f =
      lift (constantComponent A a) (constantComponent B b) ≫ g) : f = g := by
  rw [← cancel_epi (componentProductIso A B).hom]
  apply component_hom_ext
  rintro ⟨a, b⟩
  simpa using h a b

/-- Two morphisms out of a triple product of coproducts agree as soon as they agree on every
triple of components. -/
lemma triple_hom_ext {A B C : Type v} [Small.{u} A] [Small.{u} B] [Small.{u} C]
    {X : Over (⊤_ Scheme.{u})}
    (f g : (constantSchemeOverIntegersObj A ⊗ constantSchemeOverIntegersObj B) ⊗
      constantSchemeOverIntegersObj C ⟶ X)
    (h : ∀ a b c, lift (lift (constantComponent A a) (constantComponent B b))
      (constantComponent C c) ≫ f =
        lift (lift (constantComponent A a) (constantComponent B b))
          (constantComponent C c) ≫ g) : f = g := by
  rw [← cancel_epi ((componentProductIso A B).hom ▷ constantSchemeOverIntegersObj C)]
  apply pair_hom_ext
  rintro ⟨a, b⟩ c
  simpa using h a b c

/-- The multiplication on the coproduct induced by the group law on the index type. -/
def componentMul (G : Type v) [Small.{u} G] [Group G] :
    constantSchemeOverIntegersObj G ⊗ constantSchemeOverIntegersObj G ⟶
      constantSchemeOverIntegersObj G :=
  (componentProductIso G G).inv ≫ componentDesc (fun p : G × G ↦ constantComponent G (p.1 * p.2))

/-- The multiplication `componentMul G` sends the pair of components indexed by `g` and `h` to
the component indexed by `g * h`. -/
@[reassoc (attr := simp)]
lemma component_mul (G : Type v) [Small.{u} G] [Group G] (g h : G) :
    lift (constantComponent G g) (constantComponent G h) ≫ componentMul G =
      constantComponent G (g * h) := by
  rw [← component_product_hom G G g h]
  simp only [componentMul, Category.assoc, Iso.hom_inv_id_assoc, component_desc]

/-- The component indexed by `1` is a left unit for `componentMul G`. -/
lemma component_one_mul (G : Type v) [Small.{u} G] [Group G] :
    constantComponent G 1 ▷ constantSchemeOverIntegersObj G ≫ componentMul G =
      (λ_ (constantSchemeOverIntegersObj G)).hom := by
  rw [← cancel_epi (λ_ (constantSchemeOverIntegersObj G)).inv]
  apply component_hom_ext
  intro g
  have h : constantComponent G g ≫ (λ_ (constantSchemeOverIntegersObj G)).inv =
      lift (𝟙 unitObj) (constantComponent G g) := by
    rw [Iso.comp_inv_eq]
    simp only [lift_leftUnitor_hom]
  simp [← Category.assoc, h]

/-- The component indexed by `1` is a right unit for `componentMul G`. -/
lemma component_mul_one (G : Type v) [Small.{u} G] [Group G] :
    constantSchemeOverIntegersObj G ◁ constantComponent G 1 ≫ componentMul G =
      (ρ_ (constantSchemeOverIntegersObj G)).hom := by
  rw [← cancel_epi (ρ_ (constantSchemeOverIntegersObj G)).inv]
  apply component_hom_ext
  intro g
  have h : constantComponent G g ≫ (ρ_ (constantSchemeOverIntegersObj G)).inv =
      lift (constantComponent G g) (𝟙 unitObj) := by
    rw [Iso.comp_inv_eq]
    simp only [lift_rightUnitor_hom]
  simp [← Category.assoc, h]

/-- The multiplication `componentMul G` is associative. -/
lemma component_associativity (G : Type v) [Small.{u} G] [Group G] :
    componentMul G ▷ constantSchemeOverIntegersObj G ≫ componentMul G =
      (α_ (constantSchemeOverIntegersObj G) (constantSchemeOverIntegersObj G)
        (constantSchemeOverIntegersObj G)).hom ≫
      constantSchemeOverIntegersObj G ◁ componentMul G ≫ componentMul G := by
  apply triple_hom_ext
  intro g h k
  simp [mul_assoc]

/-- The group-object structure on the coproduct whose multiplication is induced by the group law
on the index type. -/
@[instance_reducible]
def componentGrpObj (G : Type v) [Small.{u} G] [Group G] :
    GrpObj (constantSchemeOverIntegersObj G) where
  one := constantComponent G 1
  mul := componentMul G
  one_mul := component_one_mul G
  mul_one := component_mul_one G
  mul_assoc := component_associativity G
  inv := componentDesc (fun g : G ↦ constantComponent G g⁻¹)
  left_inv := by
    apply component_hom_ext
    intro g
    simp [comp_lift_assoc, show toUnit unitObj = 𝟙 unitObj from toUnit_unique _ _]
  right_inv := by
    apply component_hom_ext
    intro g
    simp [comp_lift_assoc, show toUnit unitObj = 𝟙 unitObj from toUnit_unique _ _]

/-- There is a group-object structure on the coproduct satisfying
`IsConstantGroupSchemeStructure G`. -/
lemma component_structure_exists (G : Type v) [Small.{u} G] [Group G] :
    Nonempty { s : GrpObj (constantSchemeOverIntegersObj G) //
      IsConstantGroupSchemeStructure G s } :=
  ⟨⟨componentGrpObj G, component_mul G⟩⟩

end ConstantGroupScheme

/-- The group-object structure on the coproduct of copies of `Spec ℤ` indexed by `G`, whose
multiplication sends the component `(g, h)` to the component `g * h`. -/
@[stacks 03YW "constant_group_scheme_construction"]
def constantGroupSchemeStructure (G : Type v) [Small.{u} G] [Group G] :
    { s : GrpObj (constantSchemeOverIntegersObj G) // IsConstantGroupSchemeStructure G s } :=
  Classical.choice (ConstantGroupScheme.component_structure_exists G)

/-- The canonical group structure on the coproduct over `Spec ℤ`. -/
instance constantSchemeOverIntegersGrpObj (G : Type v) [Small.{u} G] [Group G] :
    GrpObj (constantSchemeOverIntegersObj G) :=
  (constantGroupSchemeStructure G).1

/-- The constant group scheme `G_S`, obtained by base-changing `G_{Spec ℤ}` to `S`. -/
@[stacks 03YW "constant_group_scheme_construction", sga "3 VIII 1.0.3"]
abbrev constantGroupScheme (G : Type v) [Small.{u} G] [Group G] (S : Scheme.{u}) :
    Grp (Over S) :=
  (Over.pullback (terminal.from S)).mapGrp.obj ⟨constantSchemeOverIntegersObj G⟩

/-- The group-valued functor sending a scheme `T` to the group of locally constant maps
`T → G`. Its action on a morphism is precomposition. -/
def locallyConstantMaps (G : Type v) [Group G] : Scheme.{u}ᵒᵖ ⥤ GrpCat.{max u v} where
  obj T := GrpCat.of (LocallyConstant T.unop G)
  map f := GrpCat.ofHom (LocallyConstant.comapMonoidHom f.unop.base.hom)
  map_id T := by
    ext f x
    rfl
  map_comp f g := by
    ext h x
    rfl

/-- The group-valued functor taking an `S`-scheme to its group of locally constant maps to
`G`, with pullback of functions on morphisms. -/
def locallyConstantMapsOver (G : Type v) [Group G] (S : Scheme.{u}) :
    Functor (Over S)ᵒᵖ GrpCat.{max u v} where
  obj T := GrpCat.of (LocallyConstant T.unop.left G)
  map f := GrpCat.ofHom
    (LocallyConstant.comapMonoidHom ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id T := by
    ext g x
    rfl
  map_comp f g := by
    ext h x
    rfl

/-- Locally constant maps, viewed on schemes over the terminal scheme. -/
abbrev locallyConstantMapsOverIntegers (G : Type v) [Group G] :
    (Over (⊤_ Scheme.{u}))ᵒᵖ ⥤ GrpCat.{max u v} :=
  locallyConstantMapsOver G (⊤_ Scheme.{u})

/-- The open subset of `T` on which a locally constant map takes the value `g`. -/
def fiberOpen (G : Type v) [Group G] {T : Scheme.{u}} (f : LocallyConstant T G) (g : G) :
    T.Opens :=
  ⟨{x | f x = g}, f.isLocallyConstant.isOpen_fiber g⟩

/-- The open cover of `T` by the fibres of a locally constant map. -/
def fiberCover (G : Type v) [Group G] {T : Scheme.{u}} (f : LocallyConstant T G) :
    T.OpenCover where
  I₀ := G
  X g := fiberOpen G f g
  f g := (fiberOpen G f g).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩

/-- The locally constant map attached to a morphism into the coproduct, sending a point to the
index of the component it lands in. -/
def indexMap (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (f : T ⟶ constantSchemeOverIntegers G) : LocallyConstant T G where
  toFun x := (sigmaOpenCover (fun _ : G ↦ (⊤_ Scheme.{u}))).idx (f x)
  isLocallyConstant := by
    refine IsLocallyConstant.iff_isOpen_fiber.mpr (fun g ↦ ?_)
    let 𝒰 := sigmaOpenCover (fun _ : G ↦ (⊤_ Scheme.{u}))
    have : IsOpenImmersion (𝒰.f g) := 𝒰.map_prop g
    have heq (y : 𝒰.X g) : 𝒰.idx (𝒰.f g y) = g := by
      obtain ⟨z, hz⟩ := 𝒰.covers (𝒰.f g y)
      have hh : Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) (𝒰.idx (𝒰.f g y)) z =
          Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g y := by
        convert hz using 1 <;> simp only [𝒰, sigmaOpenCover_f] <;> rfl
      exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : G ↦ (⊤_ Scheme.{u})) _ _ _ _).mp hh)
    have hU : {y : constantSchemeOverIntegers G | 𝒰.idx y = g} = (𝒰.f g).opensRange := by
      ext y
      constructor
      · intro hy
        obtain ⟨z, hz⟩ := 𝒰.covers y
        exact hy ▸ ⟨z, hz⟩
      · rintro ⟨z, rfl⟩
        exact heq z
    change IsOpen (f.base.hom ⁻¹' {y | 𝒰.idx y = g})
    rw [hU]
    exact (𝒰.f g).opensRange.isOpen.preimage f.base.hom.continuous

namespace ConstantGroupScheme

/-- On the fibre where a locally constant map takes the value `g`, the gluing datum is the
inclusion of the component indexed by `g`. -/
def fiberι (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (f : LocallyConstant T G) (g : G) :
    (fiberCover G f).X g ⟶ constantSchemeOverIntegers G :=
  terminal.from _ ≫ Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g

/-- The morphisms `fiberι G f` agree on the overlaps of the open cover `fiberCover G f`. -/
lemma fiberι_compat (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (f : LocallyConstant T G) (g h : G) :
    pullback.fst ((fiberCover G f).f g) ((fiberCover G f).f h) ≫ fiberι G f g =
      pullback.snd _ _ ≫ fiberι G f h := by
  let 𝒰 := fiberCover G f
  by_cases e : g = h
  · subst h
    simpa only [fiberι, Category.assoc] using congrArg
      (fun q : pullback (𝒰.f g) (𝒰.f g) ⟶ (⊤_ Scheme.{u}) ↦
        q ≫ Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g)
      (Subsingleton.elim
        (pullback.fst (𝒰.f g) (𝒰.f g) ≫ terminal.from _)
        (pullback.snd (𝒰.f g) (𝒰.f g) ≫ terminal.from _))
  · let hEmpty : IsEmpty ↑(pullback (𝒰.f g) (𝒰.f h)) := by
      refine ⟨fun x ↦ e ?_⟩
      have hx : (𝒰.f g) ((pullback.fst (𝒰.f g) (𝒰.f h)) x) =
          (𝒰.f h) ((pullback.snd (𝒰.f g) (𝒰.f h)) x) :=
        congrArg (fun m : pullback (𝒰.f g) (𝒰.f h) ⟶ T ↦ m x)
          (pullback.condition : pullback.fst (𝒰.f g) (𝒰.f h) ≫ 𝒰.f g =
            pullback.snd (𝒰.f g) (𝒰.f h) ≫ 𝒰.f h)
      have hg : f ((𝒰.f g) ((pullback.fst (𝒰.f g) (𝒰.f h)) x)) = g :=
        ((pullback.fst (𝒰.f g) (𝒰.f h)) x).property
      have hh : f ((𝒰.f h) ((pullback.snd (𝒰.f g) (𝒰.f h)) x)) = h :=
        ((pullback.snd (𝒰.f g) (𝒰.f h)) x).property
      exact hg.symm.trans ((congrArg f hx).trans hh)
    exact (isInitialOfIsEmpty (X := pullback (𝒰.f g) (𝒰.f h))).hom_ext _ _

end ConstantGroupScheme

/-- The morphism into the coproduct attached to a locally constant map, obtained by gluing the
component inclusions over the fibres. -/
def ofIndexMap (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (f : LocallyConstant T G) : T ⟶ constantSchemeOverIntegers G :=
  (fiberCover G f).glueMorphisms (ConstantGroupScheme.fiberι G f)
    (ConstantGroupScheme.fiberι_compat G f)

/-- Every point of the component indexed by `g` has index `g`. -/
lemma indexMap_component (G : Type v) [Small.{u} G] [Group G] (g : G) (x : (⊤_ Scheme.{u})) :
    indexMap G (Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g) x = g := by
  let 𝒰 := sigmaOpenCover (fun _ : G ↦ (⊤_ Scheme.{u}))
  change 𝒰.idx ((Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g) x) = g
  obtain ⟨z, hz⟩ := 𝒰.covers ((Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g) x)
  have hh : Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u}))
      (𝒰.idx ((Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g) x)) z =
      Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g x := by
    convert hz using 1
    rfl
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : G ↦ (⊤_ Scheme.{u})) _ _ _ _).mp hh)

/-- The locally constant map attached to `ofIndexMap G f` is `f`. -/
lemma indexMap_ofIndexMap (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (f : LocallyConstant T G) : indexMap G (ofIndexMap G f) = f := by
  ext x
  let 𝒰 := fiberCover G f
  obtain ⟨g, y, rfl⟩ := 𝒰.exists_eq x
  have hcomp : 𝒰.f g ≫ ofIndexMap G f =
      terminal.from _ ≫ Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g :=
    𝒰.ι_glueMorphisms (ConstantGroupScheme.fiberι G f)
      (ConstantGroupScheme.fiberι_compat G f) g
  rw [show f ((𝒰.f g) y) = g from y.property]
  change (sigmaOpenCover (fun _ : G ↦ (⊤_ Scheme.{u}))).idx
    ((ofIndexMap G f) ((𝒰.f g) y)) = g
  rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  exact indexMap_component G g _

/-- A point `x` has index `g` under `F` if and only if `F x` lies in the component indexed
by `g`. -/
lemma indexMap_eq_iff_mem_range (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (F : T ⟶ constantSchemeOverIntegers G) (g : G) (x : T) :
    indexMap G F x = g ↔ F x ∈ (Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g).opensRange := by
  let 𝒰 := sigmaOpenCover (fun _ : G ↦ (⊤_ Scheme.{u}))
  change 𝒰.idx (F x) = g ↔ F x ∈ (Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g).opensRange
  constructor
  · rintro rfl
    obtain ⟨z, hz⟩ := 𝒰.covers (F x)
    refine ⟨z, ?_⟩
    convert hz using 1
    rfl
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact indexMap_component G g z

/-- The morphism glued from the locally constant map `indexMap G F` is `F`. -/
lemma ofIndexMap_indexMap (G : Type v) [Small.{u} G] [Group G] {T : Scheme.{u}}
    (F : T ⟶ constantSchemeOverIntegers G) : ofIndexMap G (indexMap G F) = F := by
  let f := indexMap G F
  let 𝒰 := fiberCover G f
  apply 𝒰.hom_ext
  intro g
  have hR : Set.range (𝒰.f g ≫ F) ⊆
      (Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g).opensRange := by
    rintro y ⟨x, rfl⟩
    exact (indexMap_eq_iff_mem_range G F g ((𝒰.f g) x)).mp x.property
  let ψ := IsOpenImmersion.lift
    (Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g) (𝒰.f g ≫ F) hR
  have hF : 𝒰.f g ≫ F = ConstantGroupScheme.fiberι G f g := by
    calc
      _ = ψ ≫ Sigma.ι (fun _ : G ↦ (⊤_ Scheme.{u})) g :=
        (IsOpenImmersion.lift_fac _ _ hR).symm
      _ = ConstantGroupScheme.fiberι G f g := by
        dsimp only [ConstantGroupScheme.fiberι]
        congr 1
        exact Subsingleton.elim ψ (terminal.from _)
  exact (𝒰.ι_glueMorphisms (ConstantGroupScheme.fiberι G f)
    (ConstantGroupScheme.fiberι_compat G f) g).trans hF.symm

/-- The coproduct over the terminal scheme, as a representing object for locally constant
maps on schemes over the terminal scheme. -/
def overRepresentableBy (G : Type v) [Small.{u} G] [Group G] :
    (locallyConstantMapsOverIntegers G ⋙ forget GrpCat).RepresentableBy
      (constantSchemeOverIntegersObj G) where
  homEquiv {T} :=
    { toFun := fun f => indexMap G f.left
      invFun := fun f => Over.homMk (ofIndexMap G f) (Subsingleton.elim _ _)
      left_inv := fun f => by
        apply Over.OverMorphism.ext
        exact ofIndexMap_indexMap G f.left
      right_inv := fun f => indexMap_ofIndexMap G f }
  homEquiv_comp {T T'} f g := by
    change indexMap G (f.left ≫ g.left) =
      LocallyConstant.comap f.left.base.hom (indexMap G g.left)
    ext x
    rfl

/-- The group-object structure on the coproduct induced by representability. -/
@[instance_reducible]
def inducedGroupStructure (G : Type v) [Small.{u} G] [Group G] :
    GrpObj (constantSchemeOverIntegersObj G) :=
  GrpObj.ofRepresentableBy _ (locallyConstantMapsOverIntegers G) (overRepresentableBy G)

/-- Under `overRepresentableBy G`, the inclusion of the component indexed by `g` corresponds
to the constant map with value `g`. -/
lemma overRepresentableBy_component (G : Type v) [Small.{u} G] [Group G] (g : G) :
    (overRepresentableBy G).homEquiv (constantComponent G g) =
      LocallyConstant.const (⊤_ Scheme.{u}) g := by
  change indexMap G (constantComponent G g).left = _
  ext x
  exact indexMap_component G g x

/-- Under `overRepresentableBy G`, the product of two points for `inducedGroupStructure G`
corresponds to the pointwise product of the associated locally constant maps. -/
lemma overRepresentableBy_homEquiv_mul (G : Type v) [Small.{u} G] [Group G]
    {T : Over (⊤_ Scheme.{u})}
    (f g : T ⟶ constantSchemeOverIntegersObj G) :
    (overRepresentableBy G).homEquiv (lift f g ≫ (inducedGroupStructure G).toMonObj.mul) =
      (overRepresentableBy G).homEquiv f * (overRepresentableBy G).homEquiv g := by
  let X := constantSchemeOverIntegersObj G
  let : GrpObj X := inducedGroupStructure G
  have hμ : (overRepresentableBy G).homEquiv MonObj.mul =
      (overRepresentableBy G).homEquiv' (fst X X) *
      (overRepresentableBy G).homEquiv' (snd X X) := by
    change (overRepresentableBy G).homEquiv
      ((overRepresentableBy G).homEquiv'.symm
        ((overRepresentableBy G).homEquiv' (fst X X) *
          (overRepresentableBy G).homEquiv' (snd X X))) = _
    exact Equiv.apply_symm_apply _ _
  rw [(overRepresentableBy G).homEquiv_comp (lift f g) MonObj.mul, hμ]
  let p := lift f g
  change ((locallyConstantMapsOverIntegers G).map p.op)
    ((overRepresentableBy G).homEquiv' (fst X X) *
      (overRepresentableBy G).homEquiv' (snd X X)) = _
  rw [((locallyConstantMapsOverIntegers G).map p.op).hom.map_mul]
  have hfst : ((locallyConstantMapsOverIntegers G).map p.op).hom
      ((overRepresentableBy G).homEquiv' (fst X X)) =
      (overRepresentableBy G).homEquiv' (p ≫ fst X X) := by
    simpa using ((overRepresentableBy G).homEquiv'_comp p (fst X X)).symm
  have hsnd : ((locallyConstantMapsOverIntegers G).map p.op).hom
      ((overRepresentableBy G).homEquiv' (snd X X)) =
      (overRepresentableBy G).homEquiv' (p ≫ snd X X) := by
    simpa using ((overRepresentableBy G).homEquiv'_comp p (snd X X)).symm
  rw [hfst, hsnd, lift_fst, lift_snd]
  rfl

/-- The group-object structure induced by representability is the canonical group structure
`constantSchemeOverIntegersGrpObj G`. -/
lemma inducedGroupStructure_eq_constant (G : Type v) [Small.{u} G] [Group G] :
    inducedGroupStructure G = constantSchemeOverIntegersGrpObj G := by
  apply GrpObj.ext
  apply MonObj.ext
  apply ConstantGroupScheme.pair_hom_ext (A := G) (B := G)
  intro g h
  rw [(constantGroupSchemeStructure G).2 g h]
  apply (overRepresentableBy G).homEquiv.injective
  rw [overRepresentableBy_homEquiv_mul]
  simp only [overRepresentableBy_component]
  change (LocallyConstant.const (⊤_ Scheme.{u}) g *
      LocallyConstant.const (⊤_ Scheme.{u}) h) =
    LocallyConstant.const (⊤_ Scheme.{u}) (g * h)
  ext x
  rfl

/-- The group-valued functor-of-points isomorphism for the coproduct over the terminal
scheme. -/
def actualPointsIso (G : Type v) [Small.{u} G] [Group G] :
    (yonedaGrp.obj (⟨constantSchemeOverIntegersObj G⟩ : Grp (Over (⊤_ Scheme.{u}))) ⋙
      GrpCat.uliftFunctor.{v}) ≅ locallyConstantMapsOverIntegers G := by
  let X := constantSchemeOverIntegersObj G
  letI : GrpObj X := constantSchemeOverIntegersGrpObj G
  have hmul : (inducedGroupStructure G).toMonObj.mul = (‹GrpObj X›).toMonObj.mul :=
    congrArg (fun s : GrpObj X ↦ s.toMonObj.mul) (inducedGroupStructure_eq_constant G)
  refine NatIso.ofComponents (fun T => MulEquiv.toGrpIso
    { toEquiv :=
        { toFun := fun f => (overRepresentableBy G).homEquiv f.down
          invFun := fun f => ULift.up ((overRepresentableBy G).homEquiv.symm f)
          left_inv := fun f => congrArg ULift.up
            ((overRepresentableBy G).homEquiv.symm_apply_apply f.down)
          right_inv := (overRepresentableBy G).homEquiv.right_inv }
      map_mul' := ?_ }) ?_
  · rintro ⟨f⟩ ⟨g⟩
    change (overRepresentableBy G).homEquiv (f * g) = _
    refine Eq.trans ?_ (overRepresentableBy_homEquiv_mul G f g)
    exact congrArg (overRepresentableBy G).homEquiv
      ((CategoryTheory.Hom.mul_def f g).trans
        (congrArg (fun m => lift f g ≫ m) hmul.symm))
  · intro T T' f
    ext ⟨g⟩
    exact (overRepresentableBy G).homEquiv_comp f.unop g

/-- The canonical group-valued functor-of-points isomorphism for the constant group scheme
over `Spec ℤ`. -/
@[stacks 03YW "representability_over_integers",
  sga "3 I 1.8" "special case",
  sga "3 VIII 1.3" "special case",
  sga "3 VIII 1.4" "special case"]
def constantSchemeOverIntegersPointsIsoLocallyConstantMaps (G : Type v) [Small.{u} G] [Group G] :
    (yonedaGrp.obj (⟨constantSchemeOverIntegersObj G⟩ : Grp (Over (⊤_ Scheme.{u}))) ⋙
      GrpCat.uliftFunctor.{v}) ≅ locallyConstantMapsOverIntegers G :=
  actualPointsIso G

/-- The canonical isomorphism sends the inclusion of the component indexed by `g` to the
constant function with value `g`. -/
@[stacks 03YW "representability_over_integers"]
theorem constantSchemeOverIntegersPointsIsoLocallyConstantMaps_component
    (G : Type v) [Small.{u} G] [Group G] (g : G) :
    ((constantSchemeOverIntegersPointsIsoLocallyConstantMaps G).hom.app
      (Opposite.op (Over.mk (𝟙 (⊤_ Scheme.{u})))))
        (ULift.up (constantComponent G g)) = LocallyConstant.const (⊤_ Scheme.{u}) g := by
  change (actualPointsIso G).hom.app (Opposite.op (Over.mk (𝟙 (⊤_ Scheme.{u}))))
      (ULift.up (constantComponent G g)) = _
  exact overRepresentableBy_component G g

/-- The functor assigning to a scheme the group of locally constant maps to `G` is represented
by the underlying scheme of the constant group scheme over `Spec ℤ`. -/
@[stacks 03YW "representability_over_integers", sga "3 VIII 1.3" "partial"]
theorem locallyConstantMaps_representableBy_constantSchemeOverIntegers
    (G : Type v) [Small.{u} G] [Group G] :
    Nonempty ((locallyConstantMaps G ⋙ forget GrpCat).RepresentableBy
      (constantSchemeOverIntegers G)) := by
  refine ⟨{ homEquiv := ?_, homEquiv_comp := ?_ }⟩
  · exact
      { toFun := indexMap G
        invFun := ofIndexMap G
        left_inv := ofIndexMap_indexMap G
        right_inv := indexMap_ofIndexMap G }
  · intro X X' f g
    change indexMap G (f ≫ g) = LocallyConstant.comap f.base.hom (indexMap G g)
    ext x
    rfl

/-- The pullback adjunction identifies maps into the base changed constant scheme. -/
private def baseChangeHomEquiv (G : Type v) [Small.{u} G] [Group G]
    (S : Scheme.{u}) (T : Over S) :
    (T ⟶ (constantGroupScheme G S).X) ≃
      ((Over.map (terminal.from S)).obj T ⟶ constantSchemeOverIntegersObj G) :=
  ((Over.mapPullbackAdj (terminal.from S)).homEquiv T
    (constantSchemeOverIntegersObj G)).symm

private lemma baseChangeHomEquiv_left (G : Type v) [Small.{u} G] [Group G]
    (S : Scheme.{u}) (T : Over S) (f : T ⟶ (constantGroupScheme G S).X) :
    (baseChangeHomEquiv G S T f).left = f.left ≫ pullback.fst _ _ := rfl

private lemma baseChangeHomEquiv_mul (G : Type v) [Small.{u} G] [Group G]
    (S : Scheme.{u}) (T : Over S) (f g : T ⟶ (constantGroupScheme G S).X) :
    baseChangeHomEquiv G S T (f * g) =
      baseChangeHomEquiv G S T f * baseChangeHomEquiv G S T g := by
  let A := constantSchemeOverIntegersObj G
  let P := Over.pullback (terminal.from S)
  let f₀ : T ⟶ (constantGroupScheme G S).X := f
  let g₀ : T ⟶ (constantGroupScheme G S).X := g
  let : GrpObj (P.obj A) := (constantGroupScheme G S).grp
  change T ⟶ P.obj A at f g
  let c := Functor.LaxMonoidal.μ (Over.pullback (terminal.from S))
    (constantSchemeOverIntegersObj G) (constantSchemeOverIntegersObj G)
  let p := pullback.fst A.hom (terminal.from S)
  have hfst := Over.μ_pullback_left_fst_fst' (f := terminal.from S) A.hom A.hom
  have hsnd := Over.μ_pullback_left_fst_snd' (f := terminal.from S) A.hom A.hom
  have hl_fst : (lift f g).left ≫ pullback.fst (P.obj A).hom (P.obj A).hom = f.left := by
    simpa only [Over.comp_left, Over.fst_left] using congrArg Over.Hom.left (lift_fst f g)
  have hl_snd : (lift f g).left ≫ pullback.snd (P.obj A).hom (P.obj A).hom = g.left := by
    simpa only [Over.comp_left, Over.snd_left] using congrArg Over.Hom.left (lift_snd f g)
  have hpair :
      (lift f g).left ≫ c.left ≫
          pullback.fst (pullback.fst A.hom A.hom ≫ A.hom) (terminal.from S) =
        pullback.lift (f.left ≫ p) (g.left ≫ p) (by apply Subsingleton.elim) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← reassoc_of% hl_fst]
      exact congrArg ((lift f g).left ≫ ·) hfst
    · rw [pullback.lift_snd, ← reassoc_of% hl_snd]
      exact congrArg ((lift f g).left ≫ ·) hsnd
  have hmap₀ : (P.map MonObj.mul).left ≫ p =
      pullback.fst (A ⊗ A).hom (terminal.from S) ≫ (MonObj.mul (X := A)).left := by
    simp only [p]
    exact pullback.lift_fst _ _ _
  have hmap : (P.map MonObj.mul).left ≫ p =
      pullback.fst (pullback.fst A.hom A.hom ≫ A.hom) (terminal.from S) ≫
        (MonObj.mul (X := A)).left := by
    simpa only [Over.tensorObj_hom] using hmap₀
  apply Over.OverMorphism.ext
  change (baseChangeHomEquiv G S T (f₀ * g₀)).left =
    (baseChangeHomEquiv G S T f₀ * baseChangeHomEquiv G S T g₀).left
  simp only [baseChangeHomEquiv_left]
  simp only [CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left]
  change ((lift f g).left ≫ c.left ≫ (P.map MonObj.mul).left) ≫ p =
    pullback.lift (f.left ≫ p) (g.left ≫ p) (by apply Subsingleton.elim) ≫
      (MonObj.mul (X := A)).left
  rw [← hpair]
  simp only [Category.assoc, hmap]

/-- The underlying bijection of points obtained from representability and base change. -/
@[sga "3 I 4.1" "special case"]
private def constantPointsSetEquiv (G : Type v) [Small.{u} G] [Group G] (S : Scheme.{u})
    (T : Over S) :
    ULift.{v} (T ⟶ (constantGroupScheme G S).X) ≃ LocallyConstant T.left G :=
  (Equiv.ulift.trans (baseChangeHomEquiv G S T)).trans
    (Equiv.ulift.symm.trans
      ((CategoryTheory.Iso.groupIsoToMulEquiv
        ((constantSchemeOverIntegersPointsIsoLocallyConstantMaps G).app
          (Opposite.op ((Over.map (terminal.from S)).obj T)))).toEquiv))

private lemma constantPointsSetEquiv_mul (G : Type v) [Small.{u} G] [Group G] (S : Scheme.{u})
    (T : Over S) (x y : ULift.{v} (T ⟶ (constantGroupScheme G S).X)) :
    constantPointsSetEquiv G S T (x * y) =
      constantPointsSetEquiv G S T x * constantPointsSetEquiv G S T y := by
  let U := (Over.map (terminal.from S)).obj T
  let R := constantSchemeOverIntegersPointsIsoLocallyConstantMaps G
  let e := CategoryTheory.Iso.groupIsoToMulEquiv (R.app (Opposite.op U))
  change e (ULift.up (baseChangeHomEquiv G S T (x.down * y.down))) =
    e (ULift.up (baseChangeHomEquiv G S T x.down)) *
      e (ULift.up (baseChangeHomEquiv G S T y.down))
  rw [baseChangeHomEquiv_mul]
  exact e.map_mul (ULift.up (baseChangeHomEquiv G S T x.down))
    (ULift.up (baseChangeHomEquiv G S T y.down))

private def constantPointsMulEquiv (G : Type v) [Small.{u} G] [Group G] (S : Scheme.{u})
    (T : Over S) :
    ULift.{v} (T ⟶ (constantGroupScheme G S).X) ≃* LocallyConstant T.left G where
  toEquiv := constantPointsSetEquiv G S T
  map_mul' := constantPointsSetEquiv_mul G S T

@[sga "3 I 4.1" "special case"]
private lemma constantPointsSetEquiv_naturality (G : Type v) [Small.{u} G] [Group G]
    (S : Scheme.{u}) {T T' : Over S} (f : T' ⟶ T)
    (x : ULift.{v} (T ⟶ (constantGroupScheme G S).X)) :
    constantPointsSetEquiv G S T' ⟨f ≫ x.down⟩ =
      ((locallyConstantMaps G).map f.left.op).hom (constantPointsSetEquiv G S T x) := by
  let U := (Over.map (terminal.from S)).obj T
  let U' := (Over.map (terminal.from S)).obj T'
  let fbar := (Over.map (terminal.from S)).map f
  let R := constantSchemeOverIntegersPointsIsoLocallyConstantMaps G
  let ρ (V : Over (⊤_ Scheme.{u})) :=
    (CategoryTheory.Iso.groupIsoToMulEquiv (R.app (Opposite.op V))).toEquiv
  have hadj := (Over.mapPullbackAdj (terminal.from S)).homEquiv_naturality_left_symm f x.down
  change baseChangeHomEquiv G S T' (f ≫ x.down) =
      fbar ≫ baseChangeHomEquiv G S T x.down at hadj
  change ρ U' (ULift.up (baseChangeHomEquiv G S T' (f ≫ x.down))) =
    (((locallyConstantMapsOverIntegers G).map fbar.op).hom)
      (ρ U (ULift.up (baseChangeHomEquiv G S T x.down)))
  rw [hadj]
  exact congrArg (fun q => q (ULift.up (baseChangeHomEquiv G S T x.down)))
    (R.hom.naturality fbar.op)

/-- The group-valued functor of points of the constant group scheme `G_S` is naturally
isomorphic to the functor of locally constant `G`-valued maps. Under this isomorphism
multiplication is pointwise multiplication of functions. -/
@[stacks 03YW "relative_functor_of_points",
  sga "3 I 1.8" "special case",
  sga "3 VIII 1.3" "partial",
  sga "3 VIII 1.4" "partial"]
def constantGroupSchemePointsIsoLocallyConstantMaps (G : Type v) [Small.{u} G] [Group G]
    (S : Scheme.{u}) :
    (yonedaGrp.obj (constantGroupScheme G S) ⋙ GrpCat.uliftFunctor.{v}) ≅
      locallyConstantMapsOver G S :=
  Classical.choice (by
    refine ⟨NatIso.ofComponents
      (fun T => (constantPointsMulEquiv G S T.unop).toGrpIso) ?_⟩
    intro T T' f
    ext x
    exact constantPointsSetEquiv_naturality G S f.unop x)

end AlgebraicGeometry
