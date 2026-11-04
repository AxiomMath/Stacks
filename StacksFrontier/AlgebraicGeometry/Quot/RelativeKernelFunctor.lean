module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion

/-!
# The relative kernel functor of a morphism of modules

Let `P` be a pullback pseudofunctor datum on a category `A` (an inverse image along every
morphism, with the comparisons for identities and composites), let `κ` be a family of test
objects over an object `a₀`, and let `φ : N ⟶ N'` be a morphism in the fibre over `a₀`.  For a
further object `M` over `a₀` the morphisms `α : i^*M ⟶ i^*N` with `α ≫ i^*φ = 0` are preserved
by restriction along the transition morphisms of test objects; they form a subfunctor of the
relative Hom functor `CategoryTheory.PullbackData.relHomFunctor`, the **relative kernel functor**
of `φ` out of `M`.

On the test schemes over an algebraic space `X`, with the inverse image of `𝒪`-modules of
Stacks 03LU, and with `M = 𝒪_X` and `φ` the map from the degree-zero opcycles of a complex `K` of
`𝒪_X`-modules to its degree-one term, the relative kernel functor sends a test scheme `g : T ⟶ X`
to the global sections of the kernel of `g^*(K⁰/d K⁻¹) ⟶ g^*K¹`, which is the degree-zero
cohomology sheaf `H⁰(g^*K)` because `g^*` is right exact.  This is the functor of Stacks 08JX,
part (1), once `K` computes the derived pullbacks, which a K-flat complex with flat terms does
(Stacks 06YY).

## Main definitions

* `CategoryTheory.PullbackData.relKerFunctor`: the relative kernel functor.
* `CategoryTheory.PullbackData.relKerMap`: its functoriality in a commutative square.
* `AlgebraicGeometry.Space.kerSectionsFunctor`: the relative kernel functor on the test schemes
  over an algebraic space, for the inverse image of `𝒪`-modules.
* `AlgebraicGeometry.Space.degreeZeroSectionsFunctor`: the functor
  `(g : T ⟶ X) ↦ Γ(T, H⁰(g^*K))` of a complex of `𝒪_X`-modules.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]

/-- Conjugation commutes with precomposition by the image of a morphism. -/
theorem conjHom_map_comp {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    {M' M N : C} (ψ : M' ⟶ M) (α : P₁.obj M ⟶ P₁.obj N) :
    conjHom e (P₁.map ψ ≫ α) = P₂.map ψ ≫ conjHom e α := by
  simp only [conjHom, Functor.map_comp, ← Category.assoc]
  congr 2
  exact (e.hom.naturality ψ).symm

/-- Conjugation carries the zero morphism to the zero morphism. -/
theorem conjHom_zero_of_preservesZeroMorphisms [HasZeroMorphisms D₁] [HasZeroMorphisms D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L : D₁ ⥤ D₂} [L.PreservesZeroMorphisms] (e : P₂ ≅ P₁ ⋙ L) {M N : C} :
    conjHom e (0 : P₁.obj M ⟶ P₁.obj N) = 0 := by
  simp [conjHom]

end CategoryTheory.Functor

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  [∀ a, Abelian (D a)] (P : PullbackData A D)
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms]
  {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- The morphisms `α : i^*M ⟶ i^*N` killed by the inverse image of `φ : N ⟶ N'`. -/
abbrev relKerObj (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀} (φ : N ⟶ N') (i : I) : Type v₂ :=
  {α : P.relHomObj κ M N i // α ≫ (P.pull (κ.leg i)).map φ = 0}

omit [∀ a, Abelian (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms] in
/-- Restriction commutes with postcomposition by the inverse image of a morphism. -/
theorem relHomMap_comp_map (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀} (φ : N ⟶ N') {j i : I}
    (g : j ⟶ i) (α : P.relHomObj κ M N i) :
    P.relHomMap κ M N g α ≫ (P.pull (κ.leg j)).map φ =
      P.relHomMap κ M N' g (α ≫ (P.pull (κ.leg i)).map φ) :=
  (Functor.conjHom_comp_map _ φ α).symm

omit [∀ a, Abelian (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms] in
/-- Restriction commutes with precomposition by the inverse image of a morphism. -/
theorem map_comp_relHomMap (κ : ConeTo π a₀) {M' M : D a₀} (ψ : M' ⟶ M) (N : D a₀) {j i : I}
    (g : j ⟶ i) (α : P.relHomObj κ M N i) :
    (P.pull (κ.leg j)).map ψ ≫ P.relHomMap κ M N g α =
      P.relHomMap κ M' N g ((P.pull (κ.leg i)).map ψ ≫ α) :=
  (Functor.conjHom_map_comp _ ψ α).symm

/-- The restriction of a morphism killed by the inverse image of `φ` is again killed by it. -/
theorem relHomMap_mem (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀} (φ : N ⟶ N') {j i : I}
    (g : j ⟶ i) (α : P.relKerObj κ M φ i) :
    P.relHomMap κ M N g α.1 ≫ (P.pull (κ.leg j)).map φ = 0 := by
  rw [relHomMap_comp_map, α.2]
  exact Functor.conjHom_zero_of_preservesZeroMorphisms _

/-- **The relative kernel functor**: the subfunctor of the relative Hom functor of `M` and `N`
consisting of the morphisms killed by the inverse image of `φ : N ⟶ N'`. -/
def relKerFunctor (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀} (φ : N ⟶ N') :
    Iᵒᵖ ⥤ Type v₂ where
  obj i := P.relKerObj κ M φ i.unop
  map g := ↾fun α => ⟨P.relHomMap κ M N g.unop α.1, P.relHomMap_mem κ M φ g.unop α⟩
  map_id i := by
    refine ConcreteCategory.hom_ext _ _ fun α => Subtype.ext ?_
    exact P.relHomMap_id hP κ M N i.unop α.1
  map_comp g h := by
    refine ConcreteCategory.hom_ext _ _ fun α => Subtype.ext ?_
    exact P.relHomMap_comp hP κ M N h.unop g.unop α.1

/-- The values of the relative kernel functor, as an equivalence with the kernel sets; it is the
identity. -/
def relKerFunctorObjEquiv (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀}
    (φ : N ⟶ N') (i : I) :
    (P.relKerFunctor hP κ M φ).obj (Opposite.op i) ≃ P.relKerObj κ M φ i :=
  Equiv.refl _

/-- The underlying morphism of the image of a section under
`CategoryTheory.PullbackData.relKerFunctorObjEquiv` is that of the section. -/
@[simp]
theorem relKerFunctorObjEquiv_apply_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀)
    {N N' : D a₀} (φ : N ⟶ N') (i : I) (α : (P.relKerFunctor hP κ M φ).obj (Opposite.op i)) :
    (P.relKerFunctorObjEquiv hP κ M φ i α).1 = α.1 :=
  rfl

/-- The underlying morphism of the image of an element of the kernel set under the inverse of
`CategoryTheory.PullbackData.relKerFunctorObjEquiv` is that of the element. -/
@[simp]
theorem relKerFunctorObjEquiv_symm_apply_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀)
    {N N' : D a₀} (φ : N ⟶ N') (i : I) (α : P.relKerObj κ M φ i) :
    ((P.relKerFunctorObjEquiv hP κ M φ i).symm α).1 = α.1 :=
  rfl

/-- The underlying morphism of the restriction of a section of the relative kernel functor. -/
@[simp]
theorem relKerFunctor_map_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀}
    (φ : N ⟶ N') {j i : I} (g : j ⟶ i) (α : P.relKerObj κ M φ i) :
    ((P.relKerFunctor hP κ M φ).map g.op α).1 = P.relHomMap κ M N g α.1 :=
  rfl

/-- The restriction of a section of the relative kernel functor, read through
`CategoryTheory.PullbackData.relKerFunctorObjEquiv`: the conjugate of the underlying morphism by
the comparison of the pullback pseudofunctor datum. -/
theorem relKerFunctorObjEquiv_map_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀)
    {N N' : D a₀} (φ : N ⟶ N') {j i : I} (g : Opposite.op i ⟶ Opposite.op j)
    (α : (P.relKerFunctor hP κ M φ).obj (Opposite.op i)) :
    (P.relKerFunctorObjEquiv hP κ M φ j ((P.relKerFunctor hP κ M φ).map g α)).1 =
      Functor.conjHom (P.triangle (κ.w g.unop)) (P.relKerFunctorObjEquiv hP κ M φ i α).1 :=
  rfl

/-- **The relative kernel functor is functorial in a commutative square.**  A morphism `u` of
the sources of `φ` and `φ₁` compatible with a morphism of their targets carries a morphism killed
by `φ` to one killed by `φ₁`, by postcomposition with the inverse image of `u`; together with
precomposition by the inverse image of `w : M₁ ⟶ M` this is natural in the test object. -/
def relKerMap (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ : D a₀} (w : M₁ ⟶ M) {N N' : D a₀}
    (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁) (v : N' ⟶ N₁')
    (h : φ ≫ v = u ≫ φ₁) :
    P.relKerFunctor hP κ M φ ⟶ P.relKerFunctor hP κ M₁ φ₁ where
  app i := ↾fun α => ⟨(P.pull (κ.leg i.unop)).map w ≫ α.1 ≫ (P.pull (κ.leg i.unop)).map u, by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp,
      ← Category.assoc α.1, α.2, zero_comp, comp_zero]⟩
  naturality j i g := by
    refine ConcreteCategory.hom_ext _ _ fun α => Subtype.ext ?_
    change _ ≫ P.relHomMap κ M N g.unop α.1 ≫ _ =
      P.relHomMap κ M₁ N₁ g.unop (_ ≫ α.1 ≫ _)
    rw [relHomMap_comp_map, map_comp_relHomMap]

/-- The underlying morphism of a component of `CategoryTheory.PullbackData.relKerMap`. -/
@[simp]
theorem relKerMap_app_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ : D a₀} (w : M₁ ⟶ M)
    {N N' : D a₀} (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁) (v : N' ⟶ N₁')
    (h : φ ≫ v = u ≫ φ₁) (i : I) (α : P.relKerObj κ M φ i) :
    ((P.relKerMap hP κ w φ φ₁ u v h).app (Opposite.op i) α).1 =
      (P.pull (κ.leg i)).map w ≫ α.1 ≫ (P.pull (κ.leg i)).map u :=
  rfl

/-- The component of `CategoryTheory.PullbackData.relKerMap` on the kernel sets. -/
def relKerMapFun (κ : ConeTo π a₀) {M M₁ : D a₀} (w : M₁ ⟶ M) {N N' : D a₀} (φ : N ⟶ N')
    {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁) (v : N' ⟶ N₁') (h : φ ≫ v = u ≫ φ₁) (i : I) :
    P.relKerObj κ M φ i → P.relKerObj κ M₁ φ₁ i :=
  fun α => ⟨(P.pull (κ.leg i)).map w ≫ α.1 ≫ (P.pull (κ.leg i)).map u, by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp,
      ← Category.assoc α.1, α.2, zero_comp, comp_zero]⟩

omit [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms] in
/-- `CategoryTheory.PullbackData.relKerMapFun` with the identity on the source. -/
theorem relKerMapFun_id_coe (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀} (φ : N ⟶ N')
    {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁) (v : N' ⟶ N₁') (h : φ ≫ v = u ≫ φ₁) (i : I)
    (α : P.relKerObj κ M φ i) :
    (P.relKerMapFun κ (𝟙 M) φ φ₁ u v h i α).1 = α.1 ≫ (P.pull (κ.leg i)).map u := by
  simp [relKerMapFun]

/-- **A component-wise bijective `CategoryTheory.PullbackData.relKerMap` is an isomorphism.** -/
theorem isIso_relKerMap_of_bijective (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ : D a₀}
    (w : M₁ ⟶ M) {N N' : D a₀} (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁)
    (v : N' ⟶ N₁') (h : φ ≫ v = u ≫ φ₁)
    (hb : ∀ i, Function.Bijective (P.relKerMapFun κ w φ φ₁ u v h i)) :
    IsIso (P.relKerMap hP κ w φ φ₁ u v h) := by
  have : ∀ i, IsIso ((P.relKerMap hP κ w φ φ₁ u v h).app i) := fun i =>
    (isIso_iff_bijective _).2 (hb i.unop)
  exact NatIso.isIso_of_isIso_app _

/-- `CategoryTheory.PullbackData.relKerMap` read through
`CategoryTheory.PullbackData.relKerFunctorObjEquiv`. -/
theorem relKerFunctorObjEquiv_relKerMap_app (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ : D a₀}
    (w : M₁ ⟶ M) {N N' : D a₀} (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ⟶ N₁)
    (v : N' ⟶ N₁') (h : φ ≫ v = u ≫ φ₁) (i : I)
    (α : (P.relKerFunctor hP κ M φ).obj (Opposite.op i)) :
    (P.relKerFunctorObjEquiv hP κ M₁ φ₁ i
        ((P.relKerMap hP κ w φ φ₁ u v h).app (Opposite.op i) α)).1 =
      (P.pull (κ.leg i)).map w ≫ (P.relKerFunctorObjEquiv hP κ M φ i α).1 ≫
        (P.pull (κ.leg i)).map u :=
  rfl

/-- `CategoryTheory.PullbackData.relKerMap` is compatible with composition of squares. -/
theorem relKerMap_comp (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ M₂ : D a₀} (w : M₁ ⟶ M)
    (w₁ : M₂ ⟶ M₁) {N N' : D a₀} (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁')
    {N₂ N₂' : D a₀} (φ₂ : N₂ ⟶ N₂') (u : N ⟶ N₁) (v : N' ⟶ N₁') (u₁ : N₁ ⟶ N₂)
    (v₁ : N₁' ⟶ N₂') (h : φ ≫ v = u ≫ φ₁) (h₁ : φ₁ ≫ v₁ = u₁ ≫ φ₂) :
    P.relKerMap hP κ w φ φ₁ u v h ≫ P.relKerMap hP κ w₁ φ₁ φ₂ u₁ v₁ h₁ =
      P.relKerMap hP κ (w₁ ≫ w) φ φ₂ (u ≫ u₁) (v ≫ v₁)
        (by rw [← Category.assoc, h, Category.assoc, h₁, Category.assoc]) := by
  ext i α
  refine Subtype.ext ?_
  show (P.pull (κ.leg i.unop)).map w₁ ≫ ((P.pull (κ.leg i.unop)).map w ≫ α.1 ≫
      (P.pull (κ.leg i.unop)).map u) ≫ (P.pull (κ.leg i.unop)).map u₁ =
    (P.pull (κ.leg i.unop)).map (w₁ ≫ w) ≫ α.1 ≫ (P.pull (κ.leg i.unop)).map (u ≫ u₁)
  simp only [Functor.map_comp, Category.assoc]

/-- `CategoryTheory.PullbackData.relKerMap` at identities is the identity. -/
theorem relKerMap_id (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀}
    (φ : N ⟶ N') :
    P.relKerMap hP κ (𝟙 M) φ φ (𝟙 N) (𝟙 N') (by simp) = 𝟙 _ := by
  ext i α
  refine Subtype.ext ?_
  show (P.pull (κ.leg i.unop)).map (𝟙 M) ≫ α.1 ≫ (P.pull (κ.leg i.unop)).map (𝟙 N) = α.1
  simp

/-- **The relative kernel functor is invariant under an isomorphism of squares.** -/
def relKerIso (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M₁ : D a₀} (w : M₁ ≅ M) {N N' : D a₀}
    (φ : N ⟶ N') {N₁ N₁' : D a₀} (φ₁ : N₁ ⟶ N₁') (u : N ≅ N₁) (v : N' ≅ N₁')
    (h : φ ≫ v.hom = u.hom ≫ φ₁) :
    P.relKerFunctor hP κ M φ ≅ P.relKerFunctor hP κ M₁ φ₁ where
  hom := P.relKerMap hP κ w.hom φ φ₁ u.hom v.hom h
  inv := P.relKerMap hP κ w.inv φ₁ φ u.inv v.inv (by
    rw [← cancel_epi u.hom, ← Category.assoc, ← h, Category.assoc, v.hom_inv_id,
      Category.comp_id, u.hom_inv_id_assoc])
  hom_inv_id := by
    rw [relKerMap_comp]
    simp only [Iso.inv_hom_id, Iso.hom_inv_id]
    exact relKerMap_id P hP κ M φ
  inv_hom_id := by
    rw [relKerMap_comp]
    simp only [Iso.inv_hom_id, Iso.hom_inv_id]
    exact relKerMap_id P hP κ M₁ φ₁

section Precomp

variable {I₁ : Type*} [Category* I₁] {a₁ : A}

omit [∀ a, Abelian (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms] in
/-- **Transport along a morphism of cones commutes with restriction.**  Let `Φ : I₁ ⥤ I` carry
a cone `κ₁` over `a₁` to the cone `κ` over `a₀` along `k : a₁ ⟶ a₀`.  Transporting a morphism of
inverse images along the comparison of `κ₁.leg i ≫ k = κ.leg (Φ i)`, and restricting along a
transition morphism, can be done in either order.  This is the associativity coherence of the
datum. -/
theorem transportHom_relHomMap (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I)
    (k : a₁ ⟶ a₀) (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i))
    (M N : D a₀) {j i : I₁} (g : j ⟶ i)
    (α : P.relHomObj κ₁ ((P.pull k).obj M) ((P.pull k).obj N) i) :
    Functor.transportHom (P.triangle (hκ j))
        (P.relHomMap κ₁ ((P.pull k).obj M) ((P.pull k).obj N) g α) =
      P.relHomMap κ M N (Φ.map g) (Functor.transportHom (P.triangle (hκ i)) α) := by
  have h : P.triangle (hκ j) ≪≫
        (Functor.isoWhiskerLeft (P.pull k) (P.triangle (κ₁.w g)) ≪≫
          (Functor.associator (P.pull k) (P.pull (κ₁.leg i)) (P.pull ((Φ ⋙ π).map g))).symm) =
      P.triangle (κ.w (Φ.map g)) ≪≫ Functor.isoWhiskerRight (P.triangle (hκ i))
        (P.pull ((Φ ⋙ π).map g)) := by
    rw [← Iso.trans_assoc, hP.triangle_comp (κ₁.w g) (hκ i) (κ.w (Φ.map g)) (hκ j)]
    simp
  rw [relHomMap, ← Functor.conjHom_isoWhiskerLeft (P.pull k) (P.triangle (κ₁.w g)) α]
  exact Functor.transportHom_conjHom _ _ _ _ h α

/-- A transported morphism killed by the inverse image of `φ` is killed by it. -/
theorem transportHom_comp_map_eq_zero {C : Type*} [Category* C] {D₁ : Type*} [Category* D₁]
    [HasZeroMorphisms D₁] {F G : C ⥤ D₁} (e : F ≅ G) {M N N' : C} (φ : N ⟶ N')
    (α : G.obj M ⟶ G.obj N) (hα : α ≫ G.map φ = 0) :
    Functor.transportHom e α ≫ F.map φ = 0 := by
  rw [← Functor.conjHom_comp_map]
  show Functor.transportHom e (α ≫ G.map φ) = 0
  rw [hα]
  exact Functor.conjHom_zero_of_preservesZeroMorphisms _

/-- **The relative kernel functor commutes with pulling the data back along a morphism of
cones.**  If `Φ : I₁ ⥤ I` carries the cone `κ₁` over `a₁` to the cone `κ` over `a₀` along
`k : a₁ ⟶ a₀`, the relative kernel functor of `k^*M` and `k^*φ` over `κ₁` is the relative kernel
functor of `M` and `φ` over `κ`, restricted along `Φ`. -/
def relKerPrecompIso (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I) (k : a₁ ⟶ a₀)
    (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i)) (M : D a₀)
    {N N' : D a₀} (φ : N ⟶ N') :
    P.relKerFunctor hP κ₁ ((P.pull k).obj M) ((P.pull k).map φ) ≅
      Φ.op ⋙ P.relKerFunctor hP κ M φ :=
  NatIso.ofComponents
    (fun i =>
      { hom := ↾fun α => ⟨Functor.transportHom (P.triangle (hκ i.unop)) α.1,
          transportHom_comp_map_eq_zero (P.triangle (hκ i.unop)) φ α.1 α.2⟩
        inv := ↾fun α => ⟨Functor.transportHom (P.triangle (hκ i.unop)).symm α.1,
          transportHom_comp_map_eq_zero (P.triangle (hκ i.unop)).symm φ α.1 α.2⟩
        hom_inv_id := ConcreteCategory.hom_ext _ _ fun α => Subtype.ext
          ((Functor.transportHomEquiv (P.triangle (hκ i.unop)) _ _).left_inv α.1)
        inv_hom_id := ConcreteCategory.hom_ext _ _ fun α => Subtype.ext
          ((Functor.transportHomEquiv (P.triangle (hκ i.unop)) _ _).right_inv α.1) })
    (fun {_i _i'} g => ConcreteCategory.hom_ext _ _ fun α => Subtype.ext
      (P.transportHom_relHomMap hP κ Φ k κ₁ hκ M N g.unop α.1))

/-- The underlying morphism of a component of `CategoryTheory.PullbackData.relKerPrecompIso`. -/
theorem relKerPrecompIso_hom_app_coe (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I)
    (k : a₁ ⟶ a₀) (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i))
    (M : D a₀) {N N' : D a₀} (φ : N ⟶ N') (i : I₁)
    (α : P.relKerObj κ₁ ((P.pull k).obj M) ((P.pull k).map φ) i) :
    ((P.relKerPrecompIso hP κ Φ k κ₁ hκ M φ).hom.app (Opposite.op i) α).1 =
      Functor.transportHom (P.triangle (hκ i)) α.1 :=
  rfl

end Precomp

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The relative kernel functor on the test schemes over an algebraic space.**  For
`φ : N ⟶ N'` and `M` three `𝒪_X`-modules it sends a test scheme `g : T ⟶ X` to the
homomorphisms `α : g^*M ⟶ g^*N` with `α ≫ g^*φ = 0`, the inverse image being that of
Stacks 03LU. -/
abbrev kerSectionsFunctor (M : toposModules B S hS X) {N N' : toposModules B S hS X}
    (φ : N ⟶ N') : (SchemesOver X)ᵒᵖ ⥤ Type (u + 1) :=
  (toposModulePullbackData B S hS).relKerFunctor (toposModulePullbackData_isCoherent B S hS)
    (schemesOverCone X) M φ

/-- **The degree-zero sections functor of a complex of `𝒪_X`-modules**, on a family `κ` of
algebraic spaces over `X`: it sends a member `g : T ⟶ X` to the homomorphisms
`𝒪 ⟶ g^*(K⁰/dK⁻¹)` killed by the inverse image of the map to `K¹`, which are the global
sections of the degree-zero cohomology sheaf `H⁰(g^*K)` (the inverse image is right exact).
On the test schemes over `X` the family is `AlgebraicGeometry.Space.schemesOverCone X`. -/
abbrev degreeZeroSectionsFunctor {I : Type*} [Category* I] {π : I ⥤ AlgebraicSpaces B S hS}
    (κ : PullbackData.ConeTo π X) (K : CochainComplex (toposModules B S hS X) ℤ) :
    Iᵒᵖ ⥤ Type (u + 1) :=
  (toposModulePullbackData B S hS).relKerFunctor (toposModulePullbackData_isCoherent B S hS) κ
    (SheafOfModules.unit _) (K.fromOpcycles 0 1)

/-- The test schemes over `Y'` as a cone over `Y'`, read through the test schemes over `X` along
`k : Y' ⟶ X`. -/
def schemesOverConeMap {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ X) :
    PullbackData.ConeTo ((CostructuredArrow.map k) ⋙
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) X ⋙ schemeSpaceFunctor B S hS)) Y' where
  leg T := T.hom
  w g := CostructuredArrow.w g

/-- **The relative kernel functor commutes with pulling the data back along `k : Y' ⟶ X`**: on
the test schemes over `Y'` the relative kernel functor of `k^*M` and `k^*φ` is that of `M` and
`φ` over `X`, restricted along `CostructuredArrow.map k`. -/
def kerSectionsPrecompIso {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ X) (M : toposModules B S hS X)
    {N N' : toposModules B S hS X} (φ : N ⟶ N') :
    (toposModulePullbackData B S hS).relKerFunctor (toposModulePullbackData_isCoherent B S hS)
        (schemesOverConeMap k) (((toposModulePullbackData B S hS).pull k).obj M)
        (((toposModulePullbackData B S hS).pull k).map φ) ≅
      (CostructuredArrow.map k).op ⋙ kerSectionsFunctor M φ :=
  (toposModulePullbackData B S hS).relKerPrecompIso (toposModulePullbackData_isCoherent B S hS)
    (schemesOverCone X) (CostructuredArrow.map k) k (schemesOverConeMap k) (fun _ => rfl) M φ

/-- The comparison of the inverse image along `T ⟶ Y' ⟶ X` with the iterated inverse image, as
the transport of a section of the relative kernel functor over `Y'` of the pulled-back data to
one of the relative kernel functor over `X`. -/
theorem transportHom_mem {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ X) (M : toposModules B S hS X)
    {N N' : toposModules B S hS X} (φ : N ⟶ N') (T : SchemesOver Y')
    (u : (toposModulePullbackData B S hS).pull (T.hom ≫ k) ≅
      (toposModulePullbackData B S hS).pull k ⋙ (toposModulePullbackData B S hS).pull T.hom)
    (α : ((toposModulePullbackData B S hS).pull T.hom).obj
        (((toposModulePullbackData B S hS).pull k).obj M) ⟶
      ((toposModulePullbackData B S hS).pull T.hom).obj
        (((toposModulePullbackData B S hS).pull k).obj N))
    (hα : α ≫ ((toposModulePullbackData B S hS).pull T.hom).map
      (((toposModulePullbackData B S hS).pull k).map φ) = 0) :
    Functor.transportHom u α ≫ ((toposModulePullbackData B S hS).pull (T.hom ≫ k)).map φ = 0 := by
  rw [← Functor.conjHom_comp_map]
  show Functor.transportHom u (α ≫ ((toposModulePullbackData B S hS).pull T.hom).map
      (((toposModulePullbackData B S hS).pull k).map φ)) = 0
  rw [hα]
  exact Functor.conjHom_zero_of_preservesZeroMorphisms _

end AlgebraicGeometry.Space

end
