module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfToSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFunctor
public import StacksFrontier.CategoryTheory.Sites.SheafGuitartBeckChevalley
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectComponentCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismCaseA

/-!
# The comparison of the étale site of a simplicial algebraic space with its fppf total site

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. The upper
horizontal arrow of the diagram of Stacks 0DH5 is the morphism of topoi
`h : Sh((Spaces/U)_{fppf,total}) → Sh(U_étale)` given in each simplicial degree by the comparison
`h_n = a_{U_n}` of Section 0DGE. It comes from the functor `V ↦ V/U_n` from the small étale site
`U_étale` of Section 0DE7 to the fppf total site of `U` (Section 09X8). This file builds that
functor and its compatibility with the simplicial degrees.

## Main definitions

* `AlgebraicGeometry.Space.etaleToSlice`: the functor `V ↦ V/U_n` on the component of degree `n`
  of `U_étale`.
* `AlgebraicGeometry.Space.etaleToSlicesTotal`: the functor `U_étale ⥤ (Spaces/U)_total`,
  `(n, V) ↦ V/U_n`, into the total category with objects `V/U_n` of Stacks 09X8.

## References

* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor (CoGrothendieck)
open Stacks.CategoryTheory.Hypercovering

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

section EtaleToSlices

attribute [local implicit_reducible] CoGrothendieck.ι Quiver.Hom.toLoc
  CategoryTheory.SimplicialSite.totalPseudofunctor CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete CategoryTheory.SimplicialOver.slices
  CategoryTheory.Over.mapFunctor AlgebraicGeometry.Space.etaleSimplicialSite
  AlgebraicGeometry.Space.etaleComponentsFunctor

attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-- The functor `V ↦ V/U_n` on the component of degree `n` of `U_étale`: realization followed by
the inclusion of `U_{n, spaces, étale}` into the slice over `U_n`. -/
abbrev etaleToSlice (n : SimplexCategory) : EtaleComponent A n ⥤ Over (A.left.obj (op n)) :=
  realizeFunctor n ⋙ SpacesEtale.inclusion B S hS (A.left.obj (op n))

/-- Two morphisms of the total category with objects `V/U_n` agree as soon as their simplex maps
and their underlying morphisms of algebraic spaces do. -/
theorem slicesHom_ext {X Y : Grothendieck (SimplicialOver.slices A.left)} (f g : X ⟶ Y)
    (hb : f.base = g.base) (hf : f.fiber.left = g.fiber.left) : f = g := by
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  dsimp only at hb hf
  subst hb
  congr
  exact Over.OverMorphism.ext hf

/-- In the total category with objects `V/U_n`, the underlying morphism of a composite is the
composite of the underlying morphisms. -/
@[simp]
theorem slicesHom_comp_fiber_left {X Y Z : Grothendieck (SimplicialOver.slices A.left)}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).fiber.left = f.fiber.left ≫ g.fiber.left := by
  rw [Grothendieck.comp_fiber, Over.comp_left, Over.comp_left, Over.eqToHom_left]
  simp

/-- In the total category with objects `V/U_n`, the underlying morphism of an identity is the
identity. -/
@[simp]
theorem slicesHom_id_fiber_left (X : Grothendieck (SimplicialOver.slices A.left)) :
    (Grothendieck.Hom.fiber (𝟙 X)).left = 𝟙 _ := by
  rw [Grothendieck.id_fiber, Over.eqToHom_left]
  simp

/-- The underlying morphism `V → W` of algebraic spaces of a morphism `(n, V) ⟶ (m, W)` of
`U_étale`: its fibre component followed by the projection of the base change. -/
abbrev etaleTotalHomLeft {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (f : X ⟶ Y) : (realize X.fiber).obj.left ⟶ (realize Y.fiber).obj.left :=
  f.fiber.hom.hom.left ≫ comparison f.base.unop Y.fiber

/-- The underlying morphism `V → W` of a morphism `(n, V) ⟶ (m, W)` of `U_étale` lies over the
morphism `U_n → U_m` of its simplex map. -/
theorem etaleTotalHomLeft_w {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (f : X ⟶ Y) : etaleTotalHomLeft A f ≫ (realize Y.fiber).obj.hom =
      (realize X.fiber).obj.hom ≫ A.left.map f.base :=
  (Category.assoc _ _ _).trans ((congrArg (fun t ↦ f.fiber.hom.hom.left ≫ t)
    (comparison_hom f.base.unop Y.fiber)).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ A.left.map f.base.unop.op) (Over.w f.fiber.hom.hom))))

/-- The underlying morphism of algebraic spaces of an identity of `U_étale` is the identity. -/
theorem etaleTotalHomLeft_id (X : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor) :
    etaleTotalHomLeft A (𝟙 X) = 𝟙 _ := by
  obtain ⟨⟨n⟩, x⟩ := X
  refine (congrArg (fun t ↦ _ ≫ t) (comparison_id' x)).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (fun t ↦ Over.Hom.left (InducedCategory.Hom.hom
    (InducedCategory.Hom.hom t)))
    (SimplicialSite.Morphism.totalPseudofunctor_mapId_inv_app (etaleSimplicialSite A) (op n)
      x)).trans (etaleComponent_eqToHom_left _))).trans ?_
  exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)

/-- The compositor of the total pseudofunctor of `U_étale` has, on underlying algebraic spaces,
the transport along `Index.push_comp` as its components. -/
theorem etaleTotalPseudofunctor_mapComp_inv_left {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (z : Index A l) :
    (((etaleSimplicialSite A).totalPseudofunctor.mapComp ψ.op.op.toLoc
        φ.op.op.toLoc).inv.toNatTrans.app z).hom.hom.left =
      eqToHom (congrArg (fun x : Index A n ↦ (realize x).obj.left)
        (Index.push_comp ψ φ z).symm) := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToIso.inv,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  exact etaleComponent_eqToHom_left (A := A) _

/-- The transport along `Index.push_comp` followed by the projection of the base change along a
composite is the composite of the two projections. -/
theorem eqToHom_comp_comparison_comp {k m n : SimplexCategory} (χ : k ⟶ m) (ψ : m ⟶ n)
    (z : Index A k) :
    eqToHom (congrArg (fun x : Index A n ↦ (realize x).obj.left) (Index.push_comp χ ψ z).symm) ≫
        comparison (χ ≫ ψ) z = comparison ψ (z.push χ) ≫ comparison χ z := by
  rw [comparison_comp' χ ψ z]
  simp

/-- The underlying morphism of algebraic spaces of a composite in `U_étale` is the composite of
the underlying morphisms. -/
theorem etaleTotalHomLeft_comp {X Y Z : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleTotalHomLeft A (f ≫ g) = etaleTotalHomLeft A f ≫ etaleTotalHomLeft A g := by
  change (f.fiber.hom.hom.left ≫ ((transition f.base.unop).map g.fiber).hom.hom.left ≫
      (((etaleSimplicialSite A).totalPseudofunctor.mapComp g.base.unop.op.op.toLoc
        f.base.unop.op.op.toLoc).inv.toNatTrans.app Z.fiber).hom.hom.left) ≫
      comparison (g.base.unop ≫ f.base.unop) Z.fiber =
    (f.fiber.hom.hom.left ≫ comparison f.base.unop Y.fiber) ≫
      g.fiber.hom.hom.left ≫ comparison g.base.unop Z.fiber
  rw [etaleTotalPseudofunctor_mapComp_inv_left A g.base.unop f.base.unop Z.fiber]
  refine ((Category.assoc _ _ _).trans (congrArg (fun t ↦ f.fiber.hom.hom.left ≫ t)
    ((Category.assoc _ _ _).trans (congrArg (fun t ↦ _ ≫ t)
      (eqToHom_comp_comparison_comp A g.base.unop f.base.unop Z.fiber))))).trans ?_
  refine (congrArg (fun t ↦ f.fiber.hom.hom.left ≫ t) ((Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ comparison g.base.unop Z.fiber)
      (transition_map_hom_comp f.base.unop g.fiber)))).trans ?_
  exact (congrArg (fun t ↦ f.fiber.hom.hom.left ≫ t) (Category.assoc _ _ _)).trans
    (Category.assoc _ _ _).symm

/-- Two morphisms of `U_étale` with the same simplex map agree as soon as their underlying
morphisms of algebraic spaces do: the fibre component maps into a fibre product, and is
determined by its two projections. -/
theorem etaleTotalHom_ext {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (f g : X ⟶ Y) (hb : f.base = g.base) (hl : etaleTotalHomLeft A f = etaleTotalHomLeft A g) :
    f = g := by
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  dsimp only at hb
  subst hb
  obtain rfl : ff = gf := InducedCategory.hom_ext (InducedCategory.hom_ext
    (Over.OverMorphism.ext ((isPullback_comparison fb.unop Y.fiber).hom_ext hl
      ((Over.w ff.hom.hom).trans (Over.w gf.hom.hom).symm))))
  rfl

/-- The underlying morphism of algebraic spaces of the image of a morphism of the component of
degree `n` in `U_étale` is that morphism. -/
theorem etaleTotalHomLeft_ι_map {n : SimplexCategory} {x y : EtaleComponent A n} (f : x ⟶ y) :
    etaleTotalHomLeft A ((CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map
      f) = f.hom.hom.left :=
  (Category.assoc _ _ _).trans ((congrArg (fun t ↦ f.hom.hom.left ≫ t)
    (etaleTotalHomLeft_id A ⟨op n, y⟩)).trans (Category.comp_id _))

/-- The underlying morphism of the image of a morphism of the component of degree `n` in the
total category with objects `V/U_n` is that morphism. -/
theorem slices_ι_map_fiber_left {n : SimplexCategoryᵒᵖ} {V W : Over (A.left.obj n)}
    (f : V ⟶ W) :
    ((Grothendieck.ι (SimplicialOver.slices A.left) n).map f).fiber.left = f.left := by
  rw [Grothendieck.ι_map, Over.comp_left, Over.eqToHom_left]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- **The functor `U_étale ⥤ (Spaces/U)_total`**, `(n, V) ↦ V/U_n`: a morphism `(n, V) ⟶ (m, W)`
of `U_étale` goes to its underlying morphism `V ⟶ W` of algebraic spaces, which lies over
`U(φ) : U_n ⟶ U_m`. -/
def etaleToSlicesTotal :
    CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor ⥤
      Grothendieck (SimplicialOver.slices A.left) where
  obj X := ⟨X.base, (realize X.fiber).obj⟩
  map f := ⟨f.base, Over.homMk (etaleTotalHomLeft A f) (etaleTotalHomLeft_w A f)⟩
  map_id X := slicesHom_ext A _ _ rfl ((etaleTotalHomLeft_id A X).trans
    (slicesHom_id_fiber_left A ⟨X.base, (realize X.fiber).obj⟩).symm)
  map_comp {X Y Z} f g := slicesHom_ext A _ _ rfl ((etaleTotalHomLeft_comp A f g).trans
    (slicesHom_comp_fiber_left A (X := ⟨X.base, (realize X.fiber).obj⟩)
      (Y := ⟨Y.base, (realize Y.fiber).obj⟩) (Z := ⟨Z.base, (realize Z.fiber).obj⟩)
      ⟨f.base, Over.homMk (etaleTotalHomLeft A f) (etaleTotalHomLeft_w A f)⟩
      ⟨g.base, Over.homMk (etaleTotalHomLeft A g) (etaleTotalHomLeft_w A g)⟩).symm)

/-- The functor `etaleToSlicesTotal` preserves the simplex map of a morphism. -/
theorem etaleToSlicesTotal_map_base
    {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor} (f : X ⟶ Y) :
    Grothendieck.Hom.base ((etaleToSlicesTotal A).map f) = f.base := rfl

/-- The functor `etaleToSlicesTotal` sends a morphism of `U_étale` to its underlying morphism of
algebraic spaces. -/
theorem etaleToSlicesTotal_map_fiber_left
    {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor} (f : X ⟶ Y) :
    Over.Hom.left (Grothendieck.Hom.fiber ((etaleToSlicesTotal A).map f)) =
      etaleTotalHomLeft A f := rfl

/-- The image of a morphism of the component of degree `n` of `U_étale` is the image of its
underlying morphism in the component of degree `n` of `(Spaces/U)_total`. -/
theorem etaleToSlicesTotal_map_ι {n : SimplexCategory} {x y : EtaleComponent A n} (f : x ⟶ y) :
    (etaleToSlicesTotal A).map
        ((CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map f) =
      (Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map ((etaleToSlice A n).map f) :=
  slicesHom_ext A _ _ rfl ((etaleTotalHomLeft_ι_map A f).trans
    (slices_ι_map_fiber_left A ((etaleToSlice A n).map f)).symm)

/-- The square of component inclusions commutes on the nose: both composites send an object `V`
of the component of degree `n` to `V/U_n`. -/
theorem etaleToSlice_comp_ι (n : SimplexCategory) :
    etaleToSlice A n ⋙ Grothendieck.ι (SimplicialOver.slices A.left) (op n) =
      CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n) ⋙
        etaleToSlicesTotal A :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun x y f ↦ by
    change (Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map ((etaleToSlice A n).map f) =
      𝟙 _ ≫ (etaleToSlicesTotal A).map
        ((CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map f) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact (etaleToSlicesTotal_map_ι A f).symm

/-- The square of component inclusions, as a 2-square with identity components. -/
def etaleToSlicesSquare (n : SimplexCategory) :
    TwoSquare (etaleToSlice A n)
      (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n))
      (Grothendieck.ι (SimplicialOver.slices A.left) (op n)) (etaleToSlicesTotal A) :=
  TwoSquare.mk _ _ _ _
    { app := fun _ ↦ 𝟙 _
      naturality := fun x y f ↦ by
        change (Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map
            ((etaleToSlice A n).map f) ≫ 𝟙 _ =
          𝟙 _ ≫ (etaleToSlicesTotal A).map
            ((CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map f)
        rw [Category.comp_id, Category.id_comp]
        exact (etaleToSlicesTotal_map_ι A f).symm }

/-- The components of the 2-square `etaleToSlicesSquare` are identities. -/
theorem etaleToSlicesSquare_app (n : SimplexCategory) (x : EtaleComponent A n) :
    (etaleToSlicesSquare A n).app x = 𝟙 _ :=
  rfl

/-- The natural transformation of the 2-square `etaleToSlicesSquare` is an isomorphism. -/
instance isIso_etaleToSlicesSquare (n : SimplexCategory) :
    IsIso (etaleToSlicesSquare A n) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun _ ↦ inferInstanceAs (IsIso (𝟙 _))

/-- The simplex map of a factorization through the square of component inclusions. -/
theorem etaleToSlicesSquare_factor_base {n : SimplexCategory} {W : Over (A.left.obj (op n))}
    {x : EtaleComponent A n} {Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (a : W ⟶ (etaleToSlice A n).obj x)
    (b : (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).obj x ⟶ Y) :
    CategoryTheory.Grothendieck.Hom.base
        ((Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map a ≫
          (etaleToSlicesSquare A n).app x ≫ (etaleToSlicesTotal A).map b) = b.base := by
  rw [etaleToSlicesSquare_app]
  exact (Category.id_comp _).trans (Category.id_comp _)

/-- The underlying morphism of a factorization through the square of component inclusions. -/
theorem etaleToSlicesSquare_factor_left {n : SimplexCategory} {W : Over (A.left.obj (op n))}
    {x : EtaleComponent A n} {Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor}
    (a : W ⟶ (etaleToSlice A n).obj x)
    (b : (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).obj x ⟶ Y) :
    Over.Hom.left (CategoryTheory.Grothendieck.Hom.fiber
      ((Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map a ≫
        (etaleToSlicesSquare A n).app x ≫ (etaleToSlicesTotal A).map b)) =
      a.left ≫ etaleTotalHomLeft A b := by
  rw [etaleToSlicesSquare_app]
  refine (slicesHom_comp_fiber_left A _ _).trans ?_
  refine (congrArg (· ≫ _) (slices_ι_map_fiber_left A a)).trans ?_
  have h1 := slicesHom_id_fiber_left A
    ((etaleToSlice A n ⋙ Grothendieck.ι (SimplicialOver.slices A.left) (op n)).obj x)
  have h2 := slicesHom_comp_fiber_left A
    (𝟙 ((etaleToSlice A n ⋙ Grothendieck.ι (SimplicialOver.slices A.left) (op n)).obj x))
    ((etaleToSlicesTotal A).map b)
  exact congrArg (fun t ↦ a.left ≫ t) (h2.trans ((congrArg (· ≫ _) h1).trans
    (Category.id_comp _)))

/-- **The square of component inclusions is Guitart exact.** A morphism `g` from an object `W/U_n`
of degree `n` of `(Spaces/U)_total` to the image of an object `(m, y)` of `U_étale` lies over a
simplex map `ψ : [m] ⟶ [n]`, and factors terminally through the base change of `y` along
`U(ψ)`: the factorization through the fibre product, followed by the Cartesian arrow of
`U_étale`. -/
instance guitartExact_etaleToSlicesSquare (n : SimplexCategory) :
    (etaleToSlicesSquare A n).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro W Y g
  have hw : g.fiber.left ≫ (realize Y.fiber).obj.hom = W.hom ≫ A.left.map g.base.unop.op :=
    Over.w g.fiber
  let pb := isPullback_comparison (A := A) g.base.unop Y.fiber
  let x₁ : EtaleComponent A n := (Index.push g.base.unop Y.fiber : Index A n)
  let aP : W ⟶ (etaleToSlice A n).obj x₁ :=
    Over.homMk (pb.lift g.fiber.left W.hom hw) (pb.lift_snd _ _ _)
  let bP : (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).obj x₁ ⟶ Y :=
    ⟨g.base, 𝟙 _⟩
  have h3 : etaleTotalHomLeft A bP = comparison g.base.unop Y.fiber := Category.id_comp _
  have comm : (Grothendieck.ι (SimplicialOver.slices A.left) (op n)).map aP ≫
      (etaleToSlicesSquare A n).app x₁ ≫ (etaleToSlicesTotal A).map bP = g :=
    slicesHom_ext A _ _ (etaleToSlicesSquare_factor_base A aP bP)
      ((etaleToSlicesSquare_factor_left A aP bP).trans
        ((congrArg (fun t ↦ aP.left ≫ t) h3).trans (pb.lift_fst _ _ _)))
  let P := TwoSquare.StructuredArrowRightwards.mk (etaleToSlicesSquare A n) g x₁ aP bP comm
  have hterminal : ∀ Q : (etaleToSlicesSquare A n).StructuredArrowRightwards g,
      Nonempty (Q ⟶ P) := by
    intro Q
    obtain ⟨x', a', b', hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    have hb : b'.base = g.base := (etaleToSlicesSquare_factor_base A a' b').symm.trans
      (congrArg CategoryTheory.Grothendieck.Hom.base hcomm)
    have hl : a'.left ≫ etaleTotalHomLeft A b' = g.fiber.left := by
      subst hcomm
      exact (etaleToSlicesSquare_factor_left A a' b').symm
    obtain ⟨b'b, β⟩ := b'
    dsimp only at hb hl
    subst hb
    refine ⟨StructuredArrow.homMk (CostructuredArrow.homMk β ?_) ?_⟩
    · refine etaleTotalHom_ext A _ _ (Category.id_comp _) ?_
      exact (etaleTotalHomLeft_comp A _ _).trans
        ((congrArg (· ≫ _) (etaleTotalHomLeft_ι_map A β)).trans
          (congrArg (fun t ↦ β.hom.hom.left ≫ t) h3))
    · apply CostructuredArrow.hom_ext
      change a' ≫ (etaleToSlice A n).map β = aP
      refine Over.OverMorphism.ext (pb.hom_ext ?_ ?_)
      · exact (Category.assoc _ _ _).trans (hl.trans (pb.lift_fst _ _ _).symm)
      · exact ((Category.assoc _ _ _).trans ((congrArg (fun t ↦ a'.left ≫ t)
          (Over.w ((etaleToSlice A n).map β))).trans (Over.w a'))).trans
            (pb.lift_snd _ _ _).symm
  have : Nonempty ((etaleToSlicesSquare A n).StructuredArrowRightwards g) := ⟨P⟩
  exact zigzag_isConnected fun Q₁ Q₂ ↦
    (Zigzag.of_hom (hterminal Q₁).some).trans (Zigzag.of_inv (hterminal Q₂).some)

end EtaleToSlices

end AlgebraicGeometry.Space

end
