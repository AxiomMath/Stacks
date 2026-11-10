module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.AffineFlatFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Descending morphisms of covering families to a finite stage

Let `D` be a cofiltered inverse system of affine schemes with limit `c.pt`, and let `E` and `F`
be finite families of affine schemes, flat and of finite presentation, over one stage `D.obj i`.
A morphism between the base changes of `E` and `F` to the limit already comes from a morphism at
a later stage, and two morphisms at stage `i` that agree after base change to the limit already
agree at a later stage.

## Main definitions

* `AlgebraicGeometry.FamilyHom.BaseChangeEq` says that two morphisms of families become equal
  after a given base change.

## Main results

* `AlgebraicGeometry.exists_familyHom_after_baseChange` descends a morphism of the base-changed
  families to a finite stage, with its index map unchanged.
* `AlgebraicGeometry.eventually_familyHom_eq_of_baseChange_eq` descends an equality of morphisms
  of families to a finite stage.

## Implementation notes

The statements concern a whole family at once, so each is obtained by applying the corresponding
single-morphism statement (`AlgebraicGeometry.exists_morphism_after_baseChange` and
`AlgebraicGeometry.eventually_eq_of_baseChange_eq`) componentwise and then taking a common
refinement of the finitely many stages that result, which is where
`exists_common_cone_of_finite_arrows` is used. The target of a morphism of families is indexed
by the index map, so comparing two morphisms whose index maps agree only propositionally
requires heterogeneous equality.

## References

* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe a w' w v u

namespace AlgebraicGeometry

private lemma heq_of_eq_same {α : Sort u} {x y : α} (h : x = y) : HEq x y := by cases h; rfl

private lemma exists_common_cone_of_finite_arrows
    {J : Type v} [Category.{a} J] [IsCofiltered J]
    {α : Type w} [Finite α] (i : J) (j : α → J) (f : ∀ k, j k ⟶ i) :
    ∃ (k : J) (g : k ⟶ i) (h : ∀ t, k ⟶ j t), ∀ t, h t ≫ f t = g := by
  classical
  cases nonempty_fintype α
  have hi : i ∈ insert i (Finset.image j Finset.univ) := by simp
  have hj : ∀ t, j t ∈ insert i (Finset.image j Finset.univ) := fun t => by simp
  obtain ⟨k, q, hq⟩ := IsCofiltered.inf_exists _
    (Finset.image (fun t => ⟨j t, i, hj t, hi, f t⟩) Finset.univ)
  exact ⟨k, q hi, fun t => q (hj t), fun t =>
    hq (hj t) hi (Finset.mem_image_of_mem _ (Finset.mem_univ t))⟩

/-- An affine scheme flat and of finite presentation over `T` is of finite presentation. -/
theorem IsAffineFlatOfFinitePresentation.finitePresentation {T : Scheme.{u}} {X : Over T}
    (h : IsAffineFlatOfFinitePresentation X) : AlgebraicGeometry.FinitePresentation X.hom :=
  ⟨h.2.2.2.2, h.2.2.1, h.2.2.2.1⟩

namespace FamilyHom

/-- Equality of two morphisms of families after changing the base by `p`:
their index maps agree, and the induced morphisms between the pulled-back
components agree. Heterogeneous equality accommodates the dependent target
indexed by each index map. -/
abbrev BaseChangeEq {S T : Scheme.{u}} (p : S ⟶ T)
    (E : PreZeroHypercover.{w} T) (F : PreZeroHypercover.{w'} T)
    (f g : E.Hom F) : Prop :=
  f.s₀ = g.s₀ ∧
    ∀ j : E.I₀,
      HEq ((Over.pullback p).map
          (show Over.mk (E.f j) ⟶ Over.mk (F.f (f.s₀ j)) from
            Over.homMk (f.h₀ j) (f.w₀ j)))
        ((Over.pullback p).map
          (show Over.mk (E.f j) ⟶ Over.mk (F.f (g.s₀ j)) from
            Over.homMk (g.h₀ j) (g.w₀ j)))

end FamilyHom

/-- Equality of morphisms of finite families of affine, flat, finitely presented
schemes over a limit holds already at some finite stage. -/
@[stacks 049N "covering_morphism_equality",
  sga "3 VIB 10.0" "(i)",
  sga "4 VII 5.2" "a, special case"]
theorem eventually_familyHom_eq_of_baseChange_eq
    {I : Type v} [Category.{a} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i, IsAffine (D.obj i)) (i : I)
    (E : PreZeroHypercover.{w} (D.obj i))
    (F : PreZeroHypercover.{w'} (D.obj i)) [Finite E.I₀]
    (hE : ∀ j, IsAffineFlatOfFinitePresentation (Over.mk (E.f j)))
    (hF : ∀ j, IsAffineFlatOfFinitePresentation (Over.mk (F.f j)))
    (f g : E.Hom F) (hfg : FamilyHom.BaseChangeEq (c.π.app i) E F f g) :
    ∃ (j : I) (e : j ⟶ i), FamilyHom.BaseChangeEq (D.map e) E F f g := by
  have := hD
  obtain ⟨gs, gh, gw⟩ := g
  obtain rfl : f.s₀ = gs := hfg.1
  let X (x : E.I₀) : Over (D.obj i) := Over.mk (E.f x)
  let Y (x : E.I₀) : Over (D.obj i) := Over.mk (F.f (f.s₀ x))
  let φ (x : E.I₀) : X x ⟶ Y x := Over.homMk (f.h₀ x) (f.w₀ x)
  let ψ (x : E.I₀) : X x ⟶ Y x := Over.homMk (gh x) (gw x)
  have hstage (x : E.I₀) : ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map (φ x) = (Over.pullback (D.map e)).map (ψ x) := by
    have : IsAffine (E.X x) := (hE x).1
    have : IsAffine (F.X (f.s₀ x)) := (hF (f.s₀ x)).1
    exact AlgebraicGeometry.eventually_eq_of_baseChange_eq D c hc i (X x) (Y x)
      (hE x).finitePresentation (hF (f.s₀ x)).finitePresentation (φ x) (ψ x)
      (eq_of_heq (hfg.2 x))
  choose lev arr harr using hstage
  obtain ⟨k, a, b, hab⟩ := exists_common_cone_of_finite_arrows i lev arr
  refine ⟨k, a, rfl, fun x => ?_⟩
  let η := Over.pullbackComp (D.map (b x)) (D.map (arr x))
  have hcomp :
      (Over.pullback (D.map (b x) ≫ D.map (arr x))).map (φ x) =
        (Over.pullback (D.map (b x) ≫ D.map (arr x))).map (ψ x) := by
    apply (cancel_mono (η.hom.app (Y x))).1
    calc
      (Over.pullback (D.map (b x) ≫ D.map (arr x))).map (φ x) ≫ η.hom.app (Y x) =
          η.hom.app (X x) ≫
            ((Over.pullback (D.map (arr x)) ⋙ Over.pullback (D.map (b x))).map (φ x)) :=
        η.hom.naturality (φ x)
      _ = η.hom.app (X x) ≫
            ((Over.pullback (D.map (arr x)) ⋙ Over.pullback (D.map (b x))).map (ψ x)) :=
        congrArg (fun q => η.hom.app (X x) ≫ q)
          (congrArg ((Over.pullback (D.map (b x))).map) (harr x))
      _ = (Over.pullback (D.map (b x) ≫ D.map (arr x))).map (ψ x) ≫ η.hom.app (Y x) :=
        (η.hom.naturality (ψ x)).symm
  rw [← D.map_comp, hab x] at hcomp
  exact heq_of_eq hcomp

private lemma pullbackComp_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    ((Over.pullbackComp f g).hom.app W).left ≫
      pullback.fst ((Over.pullback g).obj W).hom f ≫
        pullback.fst W.hom g =
        pullback.fst W.hom (f ≫ g) := by
  simp [Over.pullbackComp, Over.pullback, Category.assoc, Category.id_comp, Category.comp_id]

private lemma pullback_eqToHom_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (W : Over Y) :
    (eqToHom (congrArg (fun p => (Over.pullback p).obj W) h)).left ≫
        pullback.fst W.hom g = pullback.fst W.hom f := by
  cases h
  simp

/-- The comparison `Over.pullbackComp f g`, transported along `f ≫ g = f'`, followed by the
two first projections, is the first projection of the pullback along `f'`. -/
theorem pullbackComp_eqToIso_hom_left_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Z} (h : f ≫ g = f') (W : Over Z) :
    ((eqToIso (congrArg (fun q => (Over.pullback q).obj W) h)).symm ≪≫
        (Over.pullbackComp f g).app W).hom.left ≫
      pullback.fst ((Over.pullback g).obj W).hom f ≫ pullback.fst W.hom g =
      pullback.fst W.hom f' := by
  let η := (Over.pullbackComp f g).app W
  let ε := eqToIso (congrArg (fun q => (Over.pullback q).obj W) h)
  calc
    _ = ε.symm.hom.left ≫ (η.hom.left ≫
          pullback.fst ((Over.pullback g).obj W).hom f ≫ pullback.fst W.hom g) := by
      simp [η, ε]
    _ = ε.symm.hom.left ≫ pullback.fst W.hom (f ≫ g) := by
      simpa [η] using congrArg (fun q => ε.symm.hom.left ≫ q) (pullbackComp_fst f g W)
    _ = pullback.fst W.hom f' := pullback_eqToHom_fst h.symm W

/-- The inverse of the comparison `Over.pullbackComp f g`, transported along `f ≫ g = f'`,
followed by the first projection, is the composite of the two first projections. -/
theorem pullbackComp_eqToIso_inv_left_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Z} (h : f ≫ g = f') (W : Over Z) :
    ((eqToIso (congrArg (fun q => (Over.pullback q).obj W) h)).symm ≪≫
        (Over.pullbackComp f g).app W).inv.left ≫ pullback.fst W.hom f' =
      pullback.fst ((Over.pullback g).obj W).hom f ≫ pullback.fst W.hom g := by
  let η := (Over.pullbackComp f g).app W
  have hh : η.inv.left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst ((Over.pullback g).obj W).hom f ≫ pullback.fst W.hom g :=
    calc
      η.inv.left ≫ pullback.fst _ _ = η.inv.left ≫ η.hom.left ≫
          pullback.fst _ _ ≫ pullback.fst _ _ :=
        (congrArg (fun q => η.inv.left ≫ q) (pullbackComp_fst f g W)).symm
      _ = _ := by simp
  calc
    _ = η.inv.left ≫ ((eqToIso (congrArg (fun q => (Over.pullback q).obj W) h)).hom.left ≫
          pullback.fst W.hom f') := by
      simp [η]
    _ = η.inv.left ≫ pullback.fst W.hom (f ≫ g) := by
      simpa [η] using congrArg (fun q => η.inv.left ≫ q) (pullback_eqToHom_fst h W)
    _ = _ := hh

/-- Naturality of the inverse of `Over.pullbackComp f g`, transported along `f ≫ g = f'`. -/
theorem pullbackComp_eqToIso_inv_naturality
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Z} (h : f ≫ g = f') {W W' : Over Z}
    (u : W ⟶ W') :
    ((eqToIso (congrArg (fun q => (Over.pullback q).obj W) h)).symm ≪≫
        (Over.pullbackComp f g).app W).inv ≫ (Over.pullback f').map u =
      (Over.pullback f).map ((Over.pullback g).map u) ≫
        ((eqToIso (congrArg (fun q => (Over.pullback q).obj W') h)).symm ≪≫
          (Over.pullbackComp f g).app W').inv := by
  let hfun : Over.pullback (f ≫ g) = Over.pullback f' := congrArg (fun q => Over.pullback q) h
  calc
    _ = (Over.pullbackComp f g).inv.app W ≫
          ((eqToIso hfun).hom.app W ≫ (Over.pullback f').map u) := by
      simp
    _ = _ := by rw [← (eqToIso hfun).hom.naturality u]
    _ = (Over.pullback f).map ((Over.pullback g).map u) ≫
          (Over.pullbackComp f g).inv.app W' ≫ (eqToIso hfun).hom.app W' := by
      simpa only [Category.assoc, Functor.comp_map] using
        (congrArg (fun q => q ≫ (eqToIso hfun).hom.app W')
          ((Over.pullbackComp f g).inv.naturality u)).symm
    _ = _ := by simp

/-- A composite of base change comparison isomorphisms is compatible with the first
projections when each of its three factors is. -/
theorem pullback_fst_mapIso_trans_symm_trans
    {P A B Z : Scheme.{u}} {p : P ⟶ A} {q : P ⟶ B} {r : P ⟶ Z}
    {b : A ⟶ B} {a : B ⟶ Z} {e : A ⟶ Z} {W : Over Z}
    (δ : (Over.pullback e).obj W ≅ (Over.pullback b).obj ((Over.pullback a).obj W))
    (θ : (Over.pullback q).obj ((Over.pullback a).obj W) ≅
      (Over.pullback p).obj ((Over.pullback b).obj ((Over.pullback a).obj W)))
    (α : (Over.pullback q).obj ((Over.pullback a).obj W) ≅ (Over.pullback r).obj W)
    (hδ : δ.hom.left ≫ pullback.fst ((Over.pullback a).obj W).hom b ≫ pullback.fst W.hom a =
      pullback.fst W.hom e)
    (hθ : θ.inv.left ≫ pullback.fst ((Over.pullback a).obj W).hom q =
      pullback.fst ((Over.pullback b).obj ((Over.pullback a).obj W)).hom p ≫
        pullback.fst ((Over.pullback a).obj W).hom b)
    (hα : α.hom.left ≫ pullback.fst W.hom r =
      pullback.fst ((Over.pullback a).obj W).hom q ≫ pullback.fst W.hom a) :
    ((Over.pullback p).mapIso δ ≪≫ θ.symm ≪≫ α).hom.left ≫ pullback.fst W.hom r =
      pullback.fst ((Over.pullback e).obj W).hom p ≫ pullback.fst W.hom e := by
  simp only [Iso.trans_hom, Over.comp_left, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    hα, reassoc_of% hθ, overPullback_map_left_fst_assoc, hδ]

/-- A square through a composite of isomorphisms commutes when the squares through its
factors do. -/
theorem mapIso_trans_symm_trans_hom_comp
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A A₁ B B₁ : 𝒞} {P Q S T : 𝒟} (δX : A ≅ A₁) (δY : B ≅ B₁) (m : A₁ ⟶ B₁)
    (θX : P ≅ G.obj A₁) (θY : Q ≅ G.obj B₁) (α : P ≅ S) (β : Q ≅ T) {n : P ⟶ Q} {φ : S ⟶ T}
    (hmor : α.hom ≫ φ = n ≫ β.hom) (hnat : θX.inv ≫ n = G.map m ≫ θY.inv) :
    (G.mapIso δX ≪≫ θX.symm ≪≫ α).hom ≫ φ =
      G.map (δX.hom ≫ m ≫ δY.inv) ≫ (G.mapIso δY ≪≫ θY.symm ≪≫ β).hom := by
  simp [hmor, reassoc_of% hnat]

/-- A morphism of finite standard covering families of an affine inverse limit
descends to a morphism at a finite stage, with its given index map unchanged. -/
@[stacks 049N "covering_morphisms"]
theorem exists_familyHom_after_baseChange
    {I : Type v} [Category.{a} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i, IsAffine (D.obj i)) (i : I)
    (E : PreZeroHypercover.{w} (D.obj i))
    (F : PreZeroHypercover.{w'} (D.obj i))
    [Finite E.I₀]
    (hE : ∀ k, IsAffineFlatOfFinitePresentation (Over.mk (E.f k)))
    (hF : ∀ k, IsAffineFlatOfFinitePresentation (Over.mk (F.f k)))
    (f : (E.pullback₂ (c.π.app i)).Hom (F.pullback₂ (c.π.app i))) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (E.pullback₂ (D.map e)).Hom (F.pullback₂ (D.map e))),
      g.s₀ = f.s₀ ∧ ∀ k : E.I₀,
        ∃ (α : (Over.pullback (c.π.app j)).obj
            ((Over.pullback (D.map e)).obj (Over.mk (E.f k))) ≅
              (Over.pullback (c.π.app i)).obj (Over.mk (E.f k)))
          (β : (Over.pullback (c.π.app j)).obj
            ((Over.pullback (D.map e)).obj (Over.mk (F.f (g.s₀ k)))) ≅
              (Over.pullback (c.π.app i)).obj (Over.mk (F.f (g.s₀ k)))),
          (α.hom.left ≫ pullback.fst (E.f k) (c.π.app i) =
            pullback.fst ((Over.pullback (D.map e)).obj (Over.mk (E.f k))).hom
              (c.π.app j) ≫ pullback.fst (E.f k) (D.map e)) ∧
          (β.hom.left ≫ pullback.fst (F.f (g.s₀ k)) (c.π.app i) =
            pullback.fst ((Over.pullback (D.map e)).obj
              (Over.mk (F.f (g.s₀ k)))).hom (c.π.app j) ≫
                pullback.fst (F.f (g.s₀ k)) (D.map e)) ∧
          HEq (α.hom.left ≫ f.h₀ k)
            (((Over.pullback (c.π.app j)).map
              (show Over.mk ((E.pullback₂ (D.map e)).f k) ⟶
                  Over.mk ((F.pullback₂ (D.map e)).f (g.s₀ k)) from
                Over.homMk (g.h₀ k) (g.w₀ k))).left ≫ β.hom.left) := by
  have := hD
  let X (k : E.I₀) : Over (D.obj i) := Over.mk (E.f k)
  let Y (k : E.I₀) : Over (D.obj i) := Over.mk (F.f (f.s₀ k))
  let φ (k : E.I₀) : (Over.pullback (c.π.app i)).obj (X k) ⟶
      (Over.pullback (c.π.app i)).obj (Y k) :=
    Over.homMk (f.h₀ k) (f.w₀ k)
  choose lev arr mor α β hα hβ hmor using fun k =>
    exists_morphism_after_baseChange D c hc i (X k) (Y k) (hE k).finitePresentation
      (hF (f.s₀ k)).finitePresentation (φ k)
  obtain ⟨j, e, b, hb⟩ := exists_common_cone_of_finite_arrows i lev arr
  have he (k : E.I₀) : D.map (b k) ≫ D.map (arr k) = D.map e := by rw [← D.map_comp, hb k]
  let δX (k : E.I₀) : (Over.pullback (D.map e)).obj (X k) ≅
      (Over.pullback (D.map (b k))).obj ((Over.pullback (D.map (arr k))).obj (X k)) :=
    (eqToIso (congrArg (fun q => (Over.pullback q).obj (X k)) (he k))).symm ≪≫
      (Over.pullbackComp (D.map (b k)) (D.map (arr k))).app (X k)
  let δY (k : E.I₀) : (Over.pullback (D.map e)).obj (Y k) ≅
      (Over.pullback (D.map (b k))).obj ((Over.pullback (D.map (arr k))).obj (Y k)) :=
    (eqToIso (congrArg (fun q => (Over.pullback q).obj (Y k)) (he k))).symm ≪≫
      (Over.pullbackComp (D.map (b k)) (D.map (arr k))).app (Y k)
  let gm (k : E.I₀) : (Over.pullback (D.map e)).obj (X k) ⟶
      (Over.pullback (D.map e)).obj (Y k) :=
    (δX k).hom ≫ (Over.pullback (D.map (b k))).map (mor k) ≫ (δY k).inv
  let g : (E.pullback₂ (D.map e)).Hom (F.pullback₂ (D.map e)) := {
    s₀ := f.s₀
    h₀ k := (gm k).left
    w₀ k := (gm k).w }
  refine ⟨j, e, g, rfl, fun k => ?_⟩
  let θ (W : Over (D.obj (lev k))) : (Over.pullback (c.π.app (lev k))).obj W ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map (b k))).obj W) :=
    (eqToIso (congrArg (fun q => (Over.pullback q).obj W) (c.w (b k)))).symm ≪≫
      (Over.pullbackComp (c.π.app j) (D.map (b k))).app W
  let αk := (Over.pullback (c.π.app j)).mapIso (δX k) ≪≫ (θ _).symm ≪≫ α k
  let βk := (Over.pullback (c.π.app j)).mapIso (δY k) ≪≫ (θ _).symm ≪≫ β k
  refine ⟨αk, βk,
    pullback_fst_mapIso_trans_symm_trans (δX k) (θ _) (α k)
      (pullbackComp_eqToIso_hom_left_fst (he k) (X k))
      (pullbackComp_eqToIso_inv_left_fst (c.w (b k)) _) (hα k),
    pullback_fst_mapIso_trans_symm_trans (δY k) (θ _) (β k)
      (pullbackComp_eqToIso_hom_left_fst (he k) (Y k))
      (pullbackComp_eqToIso_inv_left_fst (c.w (b k)) _) (hβ k), ?_⟩
  have hsq : αk.hom ≫ φ k = (Over.pullback (c.π.app j)).map (gm k) ≫ βk.hom :=
    mapIso_trans_symm_trans_hom_comp _ (δX k) (δY k) _ (θ _) (θ _) (α k) (β k) (hmor k)
      (pullbackComp_eqToIso_inv_naturality (c.w (b k)) (mor k))
  have hX :
      ((Over.pullback (c.π.app j)).obj
        ((Over.pullback (D.map e)).obj (X k))).left =
      ((Over.pullback (c.π.app j)).obj
        (Over.mk ((E.pullback₂ (D.map e)).f k))).left := by
    change pullback (pullback.snd (E.f k) (D.map e)) (c.π.app j) =
      pullback ((E.pullback₂ (D.map e)).f k) (c.π.app j)
    rw [PreZeroHypercover.pullback₂_f]
    rfl
  have hY : ((Over.pullback (c.π.app i)).obj (Y k)).left =
      (F.pullback₂ (c.π.app i)).X (f.s₀ k) :=
    (PreZeroHypercover.pullback₂_X (c.π.app i) F (f.s₀ k)).symm
  have hleft := congrArg Over.Hom.left hsq
  have hgm : Over.homMk (g.h₀ k) (g.w₀ k) = gm k := Over.OverMorphism.ext rfl
  rw [← hgm] at hleft
  let ψ : Over.mk ((E.pullback₂ (D.map e)).f k) ⟶
      Over.mk ((F.pullback₂ (D.map e)).f (g.s₀ k)) :=
    Over.homMk (g.h₀ k) (g.w₀ k)
  have hL : HEq (αk.hom.left ≫ f.h₀ k)
      (Over.Hom.left (αk.hom ≫ φ k)) := by
    apply Quiver.heq_of_homOfEq_ext hX.symm hY.symm
    cases hX
    cases hY
    rfl
  have hR : HEq (Over.Hom.left
        ((Over.pullback (c.π.app j)).map ψ ≫ βk.hom))
      (((Over.pullback (c.π.app j)).map
        ψ).left ≫ βk.hom.left) := by
    apply Quiver.heq_of_homOfEq_ext hX rfl
    cases hX
    rfl
  exact hL.trans ((heq_of_eq hleft).trans hR)

end AlgebraicGeometry
