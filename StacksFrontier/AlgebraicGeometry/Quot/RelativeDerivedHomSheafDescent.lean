module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Descent.FlatCoproductRefinement
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertySelfProduct
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality

/-!
# Step (S) of Stacks 0DLC, part (3): the relative derived Hom functor is an fppf sheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `K`, `E` pseudo-coherent objects of
`D(𝒪_X)` whose negative extensions `Ext^i(K_V, E_V)`, `i < 0`, vanish for every `V` over `Y`.
Step (S) of the proof of Stacks 0DLC, part (3), says that `T ↦ Hom(K_T, E_T)` is an fppf sheaf
over `Y`. The source applies Stacks 0DL9 to the Čech hypercovering `X_{T_•} ⟶ X_T` of an fppf
covering `{T_i ⟶ T}`, whose degree-zero term is the disjoint union of the `X_{T_i}`. This
silently uses that a morphism in the derived category of a disjoint union is a family of
morphisms on the pieces. Stacks 0DL9, as stated in
`AlgebraicGeometry.Space.DerivedHomHypercoveringDescent`, concerns one morphism `U_0 ⟶ X` and
does not supply that fact.

This file names that fact, `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct` (proved in
`StacksFrontier/AlgebraicGeometry/Quot/DerivedHomDisjointUnionProductProof.lean`), and proves step
(S) from it: `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent_of_disjointUnion`. The
unconditional form is in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeDerivedHomSheafDescentProof.lean`. Nothing is
registered.

## Main definitions

* `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct`: for an algebraic space `V` over a
  disjoint union `W₀ = ∐ W_k` of schemes of the site, `Hom(K, E)` is the product of the
  `Hom(K|_{V_k}, E|_{V_k})` over the pieces `V_k = V ×_{W₀} W_k`.
* `AlgebraicGeometry.Space.augmentedBaseChange`: the base change `X ×_Y C` of an augmented
  simplicial algebraic space over `Y`.
* `AlgebraicGeometry.Space.restrictTest`: the restriction of a test scheme along a morphism of
  the site.

## Main results

* `AlgebraicGeometry.Space.isHypercovering_augmentedBaseChange_cechNerve`: the base change of
  the Čech nerve of an fppf covering is an fppf hypercovering, in the sense of the proposition
  `AlgebraicGeometry.Space.DerivedHomHypercoveringDescent` (Stacks 0DL9).
* `AlgebraicGeometry.Space.relativeDerivedHomOver_descent`: Stacks 0DL9 along it, read on the
  relative derived Hom functor; the identification of the restrictions along the augmentation
  cone with those of `AlgebraicGeometry.Space.relativeDerivedHomOver`.
* `AlgebraicGeometry.Space.relativeDerivedHom_single_descent`: descent of `T ↦ Hom(K_T, E_T)`
  along one fppf covering of test schemes.
* `AlgebraicGeometry.Space.relativeDerivedHom_pieces_bijective`: the functor takes disjoint
  unions to products, granted `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct`.
* `AlgebraicGeometry.Space.isFppfSheafOver_of_descent`: the fppf sheaf condition from these two
  inputs, for any functor on the test schemes.
* `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent_of_disjointUnion`: **step (S)**,
  `AlgebraicGeometry.Space.RelativeDerivedHomIsSheafOfDescent`, granted the disjoint union
  property.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DL9](https://stacks.math.columbia.edu/tag/0DL9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u w

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
    (P : PullbackData A D)

/-- **Transport along a comparison triangle commutes with conjugation**: for `b ≫ a = a'`,
`a ≫ r = z`, `a' ≫ r = z'` and `b ≫ z = z'`, conjugating a morphism of inverse images along `a`
by the comparison for `b` and transporting it along the comparison for `a'` is transporting it
along the comparison for `a` and conjugating by the comparison for `b`.  This is the
associativity coherence for `b ≫ a ≫ r`. -/
theorem transportHom_conjHom_triangle (hP : P.IsCoherent) {Z Z' W X : A} {a : Z ⟶ W}
    {a' : Z' ⟶ W} {b : Z' ⟶ Z} {r : W ⟶ X} {z : Z ⟶ X} {z' : Z' ⟶ X} (hb : b ≫ a = a')
    (h : a ≫ r = z) (h' : a' ≫ r = z') (hz : b ≫ z = z') {M N : D X}
    (β : (P.pull a).obj ((P.pull r).obj M) ⟶ (P.pull a).obj ((P.pull r).obj N)) :
    Functor.transportHom (P.triangle h') (Functor.conjHom (P.triangle hb) β) =
      Functor.conjHom (P.triangle hz) (Functor.transportHom (P.triangle h) β) := by
  rw [← Functor.conjHom_isoWhiskerLeft (P.pull r) (P.triangle hb) β]
  refine Functor.transportHom_conjHom
    (Functor.isoWhiskerLeft (P.pull r) (P.triangle hb) ≪≫ (Functor.associator _ _ _).symm)
    (P.triangle hz) (P.triangle h) (P.triangle h') ?_ β
  have hc := hP.triangle_comp hb h hz h'
  rw [← Iso.trans_assoc, hc]
  ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id]

/-- The action of the relative Hom functor on a transition morphism is conjugation by the
comparison triangle of the cone. -/
theorem relHomFunctor_map_op (hP : P.IsCoherent) {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}
    (κ : ConeTo π a₀) (M N : D a₀) {j i : I} (g : j ⟶ i) (α : P.relHomObj κ M N i) :
    (P.relHomFunctor hP κ M N).map g.op α = Functor.conjHom (P.triangle (κ.w g)) α :=
  rfl

end CategoryTheory.PullbackData

namespace CategoryTheory.Functor

/-- The transport bijection is transport. -/
theorem transportHomEquiv_apply_eq {C D₁ : Type*} [Category* C] [Category* D₁] {P R : C ⥤ D₁}
    (u : R ≅ P) (M N : C) (α : P.obj M ⟶ P.obj N) :
    Functor.transportHomEquiv u M N α = Functor.transportHom u α :=
  rfl

/-- Transporting the image of a morphism under the further functor is conjugating it. -/
theorem transportHom_map_eq_conjHom {C D₁ D₂ : Type*} [Category* C] [Category* D₁]
    [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (α : P₁.obj M ⟶ P₁.obj N) :
    Functor.transportHom e (L.map α) = Functor.conjHom e α :=
  rfl

/-- Conjugation by a comparison is transport of the image along the two components. -/
theorem conjHom_eq_homCongr {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (α : P₁.obj M ⟶ P₁.obj N) :
    Functor.conjHom e α = Iso.homCongr (e.app M).symm (e.app N).symm (L.map α) :=
  rfl

/-- Conjugation by a comparison is injective: two conjugates agree exactly when the images
under the further functor agree. -/
theorem conjHom_inj_iff {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (α β : P₁.obj M ⟶ P₁.obj N) :
    Functor.conjHom e α = Functor.conjHom e β ↔ L.map α = L.map β := by
  refine ⟨fun h => (cancel_mono (e.inv.app N)).1 ((cancel_epi (e.hom.app M)).1 h),
    fun h => congrArg (fun x => e.hom.app M ≫ x ≫ e.inv.app N) h⟩

/-- Conjugation by a comparison of a morphism `L.map φ` given as a conjugate back is the
original morphism. -/
theorem conjHom_eq_of_map_eq {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (φ : P₁.obj M ⟶ P₁.obj N) (r : P₂.obj M ⟶ P₂.obj N)
    (h : L.map φ = e.inv.app M ≫ r ≫ e.hom.app N) : Functor.conjHom e φ = r := by
  show e.hom.app M ≫ L.map φ ≫ e.inv.app N = r
  rw [h]
  simp

end CategoryTheory.Functor

namespace CategoryTheory.FunctorToTypes

/-- Three restrictions of a presheaf of sets compose to the restriction along the composite. -/
theorem map_map_map_eq_of_comp_eq {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*) {a b c d : C}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (w : a ⟶ d) (h : x ≫ y ≫ z = w)
    (ξ : F.obj (Opposite.op d)) : F.map x.op (F.map y.op (F.map z.op ξ)) = F.map w.op ξ := by
  subst h
  simp only [op_comp, FunctorToTypes.map_comp_apply]

/-- Restricting along `a` and comparing with the restriction along the inverse of an
isomorphism `e` is restricting along `e.hom ≫ a`. -/
theorem map_eq_map_inv_iff {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*) {U U' W : C}
    (e : U ≅ U') (a : U' ⟶ W) (b : U ⟶ W) (h : e.hom ≫ a = b) (x : F.obj (Opposite.op W))
    (ψ : F.obj (Opposite.op U)) : F.map a.op x = F.map e.inv.op ψ ↔ F.map b.op x = ψ := by
  subst h
  constructor
  · intro h₁
    rw [op_comp, FunctorToTypes.map_comp_apply, h₁, ← FunctorToTypes.map_comp_apply, ← op_comp,
      e.hom_inv_id, op_id, FunctorToTypes.map_id_apply]
  · intro h₁
    rw [← h₁, op_comp, FunctorToTypes.map_comp_apply,
      ← FunctorToTypes.map_comp_apply F e.hom.op e.inv.op, ← op_comp, e.inv_hom_id, op_id,
      FunctorToTypes.map_id_apply]

end CategoryTheory.FunctorToTypes

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms in the derived category of a disjoint union -/

variable (B S hS) in
/-- **Morphisms in the derived category of a disjoint union** (internal; proved as
`AlgebraicGeometry.Space.derivedHomDisjointUnionProduct`): let `W₀` be a scheme of the site
which is the disjoint union of schemes `W_k` of the site (the coproduct in schemes, with the
given injections), let `V` be an algebraic space over `W₀` and `V_k = V ×_{W₀} W_k` its pieces,
with the projections `j_k : V_k ⟶ V`. Then for all `K`, `E` in `D(𝒪_V)` the map
`Hom(K, E) ⟶ ∏_k Hom(Lj_k^*K, Lj_k^*E)`, `φ ↦ (Lj_k^*φ)_k`, is bijective.

The `V_k` are open and closed subspaces of `V`, pairwise disjoint and covering `V`, so the small
étale topos of `V` is the product of those of the `V_k`, and so is `D(𝒪_V)`. The proof of
Stacks 0DLC uses this, without comment, to read a family of morphisms on the members of an fppf
covering as one morphism on their disjoint union, the degree-zero term of the Čech
hypercovering to which it applies Stacks 0DL9. The statement is unconditional: no hypothesis on
`K`, `E` is needed. The pieces are given as a base change of a disjoint union of schemes, not as a
colimit of algebraic spaces, so that the hypothesis is stable under further base change, which
is how it is used. -/
def DerivedHomDisjointUnionProduct : Prop :=
  ∀ {ι : Type u} (W : ι → BigFppfOver B S hS) (W₀ : BigFppfOver B S hS) (w : ∀ k, W k ⟶ W₀),
    IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W₀)
      fun k => (BigFppfOver.toScheme B S hS).map (w k)) →
    ∀ {V : AlgebraicSpaces B S hS} (p : V ⟶ (schemeSpaceFunctor B S hS).obj W₀)
      (V' : ι → AlgebraicSpaces B S hS) (j : ∀ k, V' k ⟶ V)
      (p' : ∀ k, V' k ⟶ (schemeSpaceFunctor B S hS).obj (W k)),
      (∀ k, IsPullback (j k) (p' k) p ((schemeSpaceFunctor B S hS).map (w k))) →
      ∀ K E : derivedModules B S hS V,
        Function.Bijective (fun φ : K ⟶ E => fun k =>
          ((smallEtaleDerivedPullbackData B S hS).pull (j k)).map φ)

/-! ### Fppf covering morphisms -/

section FppfCovering

variable {X Y Z : AlgebraicSpaces B S hS}

/-- An isomorphism of algebraic spaces is an fppf covering on its own. -/
theorem fppfCoveringMorphisms_of_isIso (e : X ⟶ Y) [IsIso e] : fppfCoveringMorphisms B S hS e := by
  have : IsIso e.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map e))
  exact isFppfCovering_of_isIso.{u, 0} B S hS Y.1 X.1 e.hom Y.2

/-- A composite of fppf covering morphisms is an fppf covering morphism. -/
theorem fppfCoveringMorphisms_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : fppfCoveringMorphisms B S hS f)
    (hg : fppfCoveringMorphisms B S hS g) : fppfCoveringMorphisms B S hS (f ≫ g) := by
  have h := isFppfCovering_comp B S hS (X := Z.1) Unit (fun _ => Unit) (fun _ => Y.1)
    (fun _ _ => X.1) (fun _ => g.hom) (fun _ _ => f.hom) hg (fun _ => hf)
  exact IsFppfCovering.reindex B S hS h (σ := fun _ : Unit => (⟨(), ()⟩ : Σ _ : Unit, Unit))
    fun ⟨(), ()⟩ => ⟨(), rfl⟩

/-- The class of fppf covering morphisms of algebraic spaces respects isomorphisms. -/
instance fppfCoveringMorphisms_respectsIso : (fppfCoveringMorphisms B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun _ _ hf => fppfCoveringMorphisms_comp _ _ (fppfCoveringMorphisms_of_isIso _) hf)
    (fun _ _ hf => fppfCoveringMorphisms_comp _ _ hf (fppfCoveringMorphisms_of_isIso _))

/-- The identity morphism of an algebraic space is an fppf covering morphism. -/
instance fppfCoveringMorphisms_containsIdentities :
    (fppfCoveringMorphisms B S hS).ContainsIdentities :=
  ⟨fun _ => fppfCoveringMorphisms_of_isIso _⟩

/-- The base change of an fppf covering morphism is an fppf covering morphism. -/
theorem fppfCoveringMorphisms_of_isPullback {W : AlgebraicSpaces B S hS} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hg : fppfCoveringMorphisms B S hS g) : fppfCoveringMorphisms B S hS fst := by
  have h₁ : fppfCoveringMorphisms B S hS (pullback.fst f g) :=
    isFppfCovering_pullback_fst B S hS (fun _ : Unit => Y) (fun _ => g) hg X f
  rw [← h.isoPullback_hom_fst]
  exact fppfCoveringMorphisms_comp _ _ (fppfCoveringMorphisms_of_isIso _) h₁

end FppfCovering

/-! ### The base change of an augmented simplicial algebraic space -/

section AugmentedBaseChange

variable {X Y : AlgebraicSpaces B S hS}

/-- An augmented simplicial algebraic space `C ⟶ C_{-1}` with a morphism `t : C_{-1} ⟶ Y`, as a
simplicial algebraic space over `Y`. -/
def augmentedOver (C : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) (t : C.right ⟶ Y) :
    SimplicialObject (Over Y) :=
  C.left.toOver Y (fun n => C.hom.app n ≫ t) (fun {n m} g => by
    have := C.hom.naturality g
    simp only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map,
      Category.comp_id] at this
    rw [← Category.assoc, this])

/-- The augmentation of `AlgebraicGeometry.Space.augmentedOver`, as morphisms over `Y`. -/
def augmentedOverHom (C : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) (t : C.right ⟶ Y)
    (n : SimplexCategoryᵒᵖ) : (augmentedOver C t).obj n ⟶ Over.mk t :=
  Over.homMk (C.hom.app n)

/-- **The base change `X ×_Y C` of an augmented simplicial algebraic space** `C ⟶ C_{-1}` over
`Y`, along `f : X ⟶ Y`: the term in degree `n` is `X_{C_n}`, the augmentation is the base change
`X_{C_n} ⟶ X_{C_{-1}}` of the augmentation of `C`. -/
def augmentedBaseChange (f : X ⟶ Y) (C : SimplicialObject.Augmented (AlgebraicSpaces B S hS))
    (t : C.right ⟶ Y) : SimplicialObject.Augmented (AlgebraicSpaces B S hS) where
  left := augmentedOver C t ⋙ overBaseChangeFunctor f ⋙ Over.forget X
  right := overBaseChange f (Over.mk t)
  hom :=
    { app := fun n => overBaseChangeMap f (augmentedOverHom C t n)
      naturality := fun {n m} g => by
        simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Functor.comp_map,
          Over.forget_map, Functor.const_obj_map]
        change overBaseChangeMap f ((augmentedOver C t).map g) ≫ _ = _
        rw [← overBaseChangeMap_comp]
        congr 1
        refine Over.OverMorphism.ext ?_
        change C.left.map g ≫ C.hom.app m = C.hom.app n
        simp }

/-- The augmentation of the base change, followed by the projection to `X`, is the projection
of the base change. -/
@[reassoc]
theorem augmentedBaseChange_hom_app_comp_projection (f : X ⟶ Y)
    (C : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) (t : C.right ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    (augmentedBaseChange f C t).hom.app n ≫ overProjection f (Over.mk t) =
      overProjection f ((augmentedOver C t).obj n) :=
  overBaseChangeMap_comp_projection f _

end AugmentedBaseChange

/-! ### The base change of a Čech nerve is an fppf hypercovering -/

section Cech

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (C : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) (t : C.right ⟶ Y)

/-- A vertex map of the base change, followed by the projection to the term of `C`, is the
vertex map of `C`. -/
@[reassoc]
theorem augmentedBaseChange_vertexMap_inclusion (n : ℕ) (i : Fin (n + 1)) :
    (augmentedBaseChange f C t).vertexMap n i ≫
        overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋0⦌)) =
      overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)) ≫ C.vertexMap n i :=
  overBaseChangeMap_comp_inclusion f ((augmentedOver C t).map _)

/-- A vertex map of the base change, followed by the projection to `X`, is the projection. -/
@[reassoc]
theorem augmentedBaseChange_vertexMap_projection (n : ℕ) (i : Fin (n + 1)) :
    (augmentedBaseChange f C t).vertexMap n i ≫
        overProjection f ((augmentedOver C t).obj (Opposite.op ⦋0⦌)) =
      overProjection f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)) :=
  overBaseChangeMap_comp_projection f ((augmentedOver C t).map _)

/-- The augmentation of the base change, followed by the projection to `C_{-1}`, is the
projection followed by the augmentation of `C`. -/
@[reassoc]
theorem augmentedBaseChange_hom_app_comp_inclusion (k : SimplexCategoryᵒᵖ) :
    (augmentedBaseChange f C t).hom.app k ≫ overInclusion f (Over.mk t) =
      overInclusion f ((augmentedOver C t).obj k) ≫ C.hom.app k :=
  overBaseChangeMap_comp_inclusion f (augmentedOverHom C t k)

variable (hC : ∀ n : ℕ, IsLimit (Fan.mk (C.over.obj (Opposite.op ⦋n⦌))
  (C.overProj C.vertexMap C.vertexMap_comp_hom n)))

include hC in
/-- **The base change of a self-product augmented simplicial algebraic space is a self-product
augmented simplicial algebraic space**: if the terms of `C` are, over `C_{-1}`, the self-products
of `C_0` through the vertex maps, then the terms of `X ×_Y C` are, over `X_{C_{-1}}`, the
self-products of `X_{C_0}`. Base change is a right adjoint. -/
def isLimitVertexFanAugmentedBaseChange (n : ℕ) :
    IsLimit (Fan.mk ((augmentedBaseChange f C t).over.obj (Opposite.op ⦋n⦌))
      ((augmentedBaseChange f C t).overProj (augmentedBaseChange f C t).vertexMap
        (augmentedBaseChange f C t).vertexMap_comp_hom n)) := by
  have hsqT : IsPullback (overProjection f (Over.mk t)) (overInclusion f (Over.mk t)) f t :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f t
  have hsqn : IsPullback (overProjection f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)))
      (overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋n⦌))) f
      (C.hom.app (Opposite.op ⦋n⦌) ≫ t) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f _
  have hinc := augmentedBaseChange_hom_app_comp_inclusion f C t
  have hpro := augmentedBaseChange_hom_app_comp_projection f C t
  have hvi := augmentedBaseChange_vertexMap_inclusion f C t n
  have hvp := augmentedBaseChange_vertexMap_projection f C t n
  -- the fan of `C` attached to a fan of the base change
  let sC : ∀ s : Fan fun _ : Fin (n + 1) =>
        (augmentedBaseChange f C t).over.obj (Opposite.op ⦋0⦌),
      Fan fun _ : Fin (n + 1) => C.over.obj (Opposite.op ⦋0⦌) := fun s =>
    Fan.mk (Over.mk (s.pt.hom ≫ overInclusion f (Over.mk t))) fun i =>
      Over.homMk ((s.proj i).left ≫
          overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋0⦌)))
        ((Category.assoc _ _ _).trans ((congrArg ((s.proj i).left ≫ ·)
          (hinc (Opposite.op ⦋0⦌)).symm).trans ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ overInclusion f (Over.mk t)) (Over.w (s.proj i))))))
  let ℓC : ∀ s : Fan fun _ : Fin (n + 1) =>
        (augmentedBaseChange f C t).over.obj (Opposite.op ⦋0⦌),
      s.pt.left ⟶ C.left.obj (Opposite.op ⦋n⦌) := fun s => ((hC n).lift (sC s)).left
  have hℓCb : ∀ s, ℓC s ≫ C.hom.app (Opposite.op ⦋n⦌) =
      s.pt.hom ≫ overInclusion f (Over.mk t) := fun s => Over.w ((hC n).lift (sC s))
  have hℓCv : ∀ s i, ℓC s ≫ C.vertexMap n i =
      (s.proj i).left ≫ overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋0⦌)) :=
    fun s i => congrArg CommaMorphism.left ((hC n).fac (sC s) ⟨i⟩)
  have hw : ∀ s : Fan fun _ : Fin (n + 1) =>
        (augmentedBaseChange f C t).over.obj (Opposite.op ⦋0⦌),
      (s.pt.hom ≫ overProjection f (Over.mk t)) ≫ f =
        ℓC s ≫ C.hom.app (Opposite.op ⦋n⦌) ≫ t := fun s =>
    (Category.assoc _ _ _).trans ((congrArg (s.pt.hom ≫ ·) hsqT.w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) (hℓCb s).symm).trans
        (Category.assoc _ _ _))))
  let ℓ : ∀ s : Fan fun _ : Fin (n + 1) =>
        (augmentedBaseChange f C t).over.obj (Opposite.op ⦋0⦌),
      s.pt.left ⟶ (augmentedBaseChange f C t).left.obj (Opposite.op ⦋n⦌) := fun s =>
    hsqn.lift (s.pt.hom ≫ overProjection f (Over.mk t)) (ℓC s) (hw s)
  have hℓp : ∀ s, ℓ s ≫ overProjection f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)) =
      s.pt.hom ≫ overProjection f (Over.mk t) := fun s => hsqn.lift_fst _ _ _
  have hℓi : ∀ s, ℓ s ≫ overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)) =
      ℓC s := fun s => hsqn.lift_snd _ _ _
  have hℓb : ∀ s, ℓ s ≫ (augmentedBaseChange f C t).hom.app (Opposite.op ⦋n⦌) = s.pt.hom :=
    fun s => overBaseChange_hom_ext f (T := Over.mk t)
      ((Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·) (hpro (Opposite.op ⦋n⦌))).trans
        (hℓp s)))
      ((Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·) (hinc (Opposite.op ⦋n⦌))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ C.hom.app (Opposite.op ⦋n⦌)) (hℓi s)).trans (hℓCb s)))))
  refine mkFanLimit _ (fun s => Over.homMk (ℓ s) (hℓb s)) (fun s i => ?_) (fun s m hm => ?_)
  · refine Over.OverMorphism.ext ?_
    exact overBaseChange_hom_ext f (T := (augmentedOver C t).obj (Opposite.op ⦋0⦌))
      ((Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·) (hvp i)).trans ((hℓp s).trans
        ((congrArg (· ≫ overProjection f (Over.mk t)) (Over.w (s.proj i))).symm.trans
          ((Category.assoc _ _ _).trans
            (congrArg ((s.proj i).left ≫ ·) (hpro (Opposite.op ⦋0⦌))))))))
      ((Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·) (hvi i)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ C.vertexMap n i) (hℓi s)).trans (hℓCv s i)))))
  · refine Over.OverMorphism.ext ?_
    have hmb : m.left ≫ (augmentedBaseChange f C t).hom.app (Opposite.op ⦋n⦌) = s.pt.hom :=
      Over.w m
    have hmv : ∀ i, m.left ≫ (augmentedBaseChange f C t).vertexMap n i = (s.proj i).left :=
      fun i => congrArg CommaMorphism.left (hm i)
    have hmC : m.left ≫ overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋n⦌)) = ℓC s :=
      C.hom_ext_of_isLimit_fan C.vertexMap C.vertexMap_comp_hom hC
        ((Category.assoc _ _ _).trans ((congrArg (m.left ≫ ·)
          (hinc (Opposite.op ⦋n⦌))).symm.trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ overInclusion f (Over.mk t)) hmb).trans (hℓCb s).symm))))
        fun i => (Category.assoc _ _ _).trans ((congrArg (m.left ≫ ·) (hvi i)).symm.trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ overInclusion f ((augmentedOver C t).obj (Opposite.op ⦋0⦌)))
              (hmv i)).trans (hℓCv s i).symm)))
    exact overBaseChange_hom_ext f (T := (augmentedOver C t).obj (Opposite.op ⦋n⦌))
      ((congrArg (m.left ≫ ·) (hpro (Opposite.op ⦋n⦌))).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ overProjection f (Over.mk t)) hmb).trans (hℓp s).symm)))
      (hmC.trans (hℓi s).symm)

/-- The algebraic spaces over `S` have finite limits: a final object and fibre products. -/
local instance : HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The projection of a one-fold wide fibre product is an isomorphism. -/
instance isIso_spaces_widePullback_π_fin_one {V T : AlgebraicSpaces B S hS} (q : V ⟶ T) :
    IsIso (WidePullback.π (fun _ : Fin 1 => q) 0) := by
  refine ⟨WidePullback.lift q (fun _ => 𝟙 V) (fun _ => Category.id_comp _), ?_,
    WidePullback.lift_π _ _ _ _ _⟩
  apply WidePullback.hom_ext
  · intro j
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

/-- **The base change of the Čech nerve of an fppf covering is an fppf hypercovering**: for an
fppf covering `q : V ⟶ T` and a morphism `t : T ⟶ Y`, the base change `X ×_Y Č(V/T) ⟶ X_T`
along `f : X ⟶ Y` is an fppf hypercovering of `X_T`. -/
theorem isHypercovering_augmentedBaseChange_cechNerve {V T : AlgebraicSpaces B S hS} (q : V ⟶ T)
    (t : T ⟶ Y) (hq : fppfCoveringMorphisms B S hS q) :
    (fppfCoveringMorphisms B S hS).IsHypercovering
      (augmentedBaseChange f (Arrow.mk q).augmentedCechNerve t) := by
  refine MorphismProperty.isHypercovering_of_isLimit_vertexFan _ _
    (fun n => isLimitVertexFanAugmentedBaseChange f (Arrow.mk q).augmentedCechNerve t
      (fun k => Arrow.isLimitVertexFanAugmentedCechNerve (Arrow.mk q) k) n) ?_
  refine fppfCoveringMorphisms_of_isPullback
    (isPullback_overBaseChangeMap f (augmentedOverHom (Arrow.mk q).augmentedCechNerve t _)) ?_
  have h := fppfCoveringMorphisms_comp _ _
    (fppfCoveringMorphisms_of_isIso (WidePullback.π (fun _ : Fin 1 => q) 0)) hq
  rw [WidePullback.π_arrow] at h
  exact h

end Cech

/-! ### Stacks 0DL9 along the base change of a Čech nerve -/

section Descent

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The algebraic spaces over `S` have finite limits: a final object and fibre products. -/
local instance : HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

variable (B S hS) in
/-- The hypotheses of step (S) on `K`, `E` over `X_T`: the pullbacks of `K` and `E` to `X_T` are
pseudo-coherent, and the negative extensions of the pullback of `K` by that of `E` vanish after
every base change. -/
structure DescentHypotheses (f : X ⟶ Y) (K E : derivedModules B S hS X) (T : Over Y) : Prop where
  /-- The pullback of `K` to `X_T` is a pseudo-coherent complex. -/
  pseudoCoherent_left : (smallEtaleRingedSite B S hS (overBaseChange f T).1
    (overBaseChange f T).2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f T)).obj K)
  /-- The pullback of `E` to `X_T` is a pseudo-coherent complex. -/
  pseudoCoherent_right : (smallEtaleRingedSite B S hS (overBaseChange f T).1
    (overBaseChange f T).2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f T)).obj E)
  /-- For every `V` over `Y` and every `i < 0`, there is at most one morphism from the pullback of
  `K` to `X_V` to the shift by `i` of the pullback of `E` to `X_V`. -/
  negExt : ∀ (V : Over Y) (i : ℤ), i < 0 →
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)

/-- **Stacks 0DL9 along the base change of the Čech nerve of an fppf covering**, read on the
relative derived Hom functor over `Y`: for an fppf covering `q : V ⟶ T` and `t : T ⟶ Y`, a
morphism `K_{C_0} ⟶ E_{C_0}` on the degree-zero term of the Čech nerve `C` of `q` whose two
restrictions to `C_1` agree is the restriction of exactly one morphism `K_T ⟶ E_T`. -/
theorem relativeDerivedHomOver_descent (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    {V T : AlgebraicSpaces B S hS} (q : V ⟶ T) (t : T ⟶ Y) (hq : fppfCoveringMorphisms B S hS q)
    (K E : derivedModules B S hS X) (hKE : DescentHypotheses B S hS f K E (Over.mk t))
    (ψ : (relativeDerivedHomOver f K E).obj
      (Opposite.op ((augmentedOver (Arrow.mk q).augmentedCechNerve t).obj
        (Opposite.op ⦋0⦌)))) :
    ((relativeDerivedHomOver f K E).map
        ((augmentedOver (Arrow.mk q).augmentedCechNerve t).map
          (SimplexCategory.δ (0 : Fin 2)).op).op ψ =
      (relativeDerivedHomOver f K E).map
        ((augmentedOver (Arrow.mk q).augmentedCechNerve t).map
          (SimplexCategory.δ (1 : Fin 2)).op).op ψ) ↔
      ∃! g : (relativeDerivedHomOver f K E).obj (Opposite.op (Over.mk t)),
        (relativeDerivedHomOver f K E).map
          (augmentedOverHom (Arrow.mk q).augmentedCechNerve t (Opposite.op ⦋0⦌)).op g = ψ := by
  have hP := smallEtaleDerivedPullbackData_isCoherent B S hS
  have hpro := augmentedBaseChange_hom_app_comp_projection f (Arrow.mk q).augmentedCechNerve t
  have hA := isHypercovering_augmentedBaseChange_cechNerve f q t hq
  have key : ∀ {Z : AlgebraicSpaces B S hS} {m m' : Z ⟶ X} (_ : m = m') (i : ℤ),
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull m').obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull m').obj E)⟦i⟧) →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull m).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull m).obj E)⟦i⟧) := by
    rintro _ _ _ rfl _ h
    exact h
  obtain ⟨-, hiff⟩ := h0DL9 (augmentedBaseChange f (Arrow.mk q).augmentedCechNerve t) hA
    (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f (Over.mk t))).obj K)
    (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f (Over.mk t))).obj E)
    hKE.pseudoCoherent_left hKE.pseudoCoherent_right (fun n i hi =>
      (subsingleton_pull_comp_iff _ _ K E i).2 (key (hpro _) i (hKE.negExt _ i hi)))
  let τ₀ := Functor.transportHomEquiv
    ((smallEtaleDerivedPullbackData B S hS).triangle (hpro (Opposite.op ⦋0⦌))) K E
  let τ₁ := Functor.transportHomEquiv
    ((smallEtaleDerivedPullbackData B S hS).triangle (hpro (Opposite.op ⦋1⦌))) K E
  have hface : ∀ k : Fin 2, τ₁ (((smallEtaleDerivedPullbackData B S hS).relHomMap
      (augmentationCone (augmentedBaseChange f (Arrow.mk q).augmentedCechNerve t))
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f (Over.mk t))).obj K)
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f (Over.mk t))).obj E)
      (SimplexCategory.δ k).op) (τ₀.symm ψ)) =
      (relativeDerivedHomOver f K E).map
        ((augmentedOver (Arrow.mk q).augmentedCechNerve t).map (SimplexCategory.δ k).op).op ψ := by
    intro k
    have hz := (overBaseChangeCone f).w
      ((augmentedOver (Arrow.mk q).augmentedCechNerve t).map (SimplexCategory.δ k).op)
    have hr : (relativeDerivedHomOver f K E).map
        ((augmentedOver (Arrow.mk q).augmentedCechNerve t).map (SimplexCategory.δ k).op).op ψ =
        Functor.conjHom ((smallEtaleDerivedPullbackData B S hS).triangle hz) ψ :=
      PullbackData.relHomFunctor_map_op _ hP (overBaseChangeCone f) K E _ ψ
    have h₁ := (smallEtaleDerivedPullbackData B S hS).transportHom_conjHom_triangle hP
      ((augmentationCone (augmentedBaseChange f (Arrow.mk q).augmentedCechNerve t)).w
        (SimplexCategory.δ k).op)
      (hpro (Opposite.op ⦋0⦌)) (hpro (Opposite.op ⦋1⦌)) hz (M := K) (N := E) (τ₀.symm ψ)
    have h₂ : Functor.transportHom ((smallEtaleDerivedPullbackData B S hS).triangle
        (hpro (Opposite.op ⦋0⦌))) (τ₀.symm ψ) = ψ :=
      (Functor.transportHomEquiv_apply_eq _ K E _).symm.trans (τ₀.apply_symm_apply ψ)
    rw [hr]
    exact (Functor.transportHomEquiv_apply_eq _ K E _).trans
      (h₁.trans (congrArg
        (Functor.conjHom ((smallEtaleDerivedPullbackData B S hS).triangle hz)) h₂))
  have e₁ := hiff (τ₀.symm ψ)
  refine Iff.trans ((Eq.congr (hface 0) (hface 1)).symm.trans τ₁.injective.eq_iff)
    (e₁.trans (existsUnique_congr fun g => ?_))
  refine (Equiv.eq_symm_apply τ₀).trans ?_
  exact Eq.congr_left ((Functor.transportHomEquiv_apply_eq _ K E _).trans
    ((Functor.transportHom_map_eq_conjHom _ g).trans
      (PullbackData.relHomFunctor_map_op _ hP (overBaseChangeCone f) K E
        (augmentedOverHom (Arrow.mk q).augmentedCechNerve t (Opposite.op ⦋0⦌)) g).symm))

end Descent

/-! ### Descent along one fppf covering of test schemes -/

section SingleDescent

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The algebraic spaces over `S` have finite limits: a final object and fibre products. -/
local instance : HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The action of the relative derived Hom functor on a morphism of test schemes is conjugation
by the comparison triangle of the base changes. -/
theorem relativeDerivedHom_map_eq (K E : derivedModules B S hS X) {U T : SchemesOver Y}
    (g : U ⟶ T) (α : (relativeDerivedHom f K E).obj (Opposite.op T)) :
    (relativeDerivedHom f K E).map g.op α =
      Functor.conjHom ((smallEtaleDerivedPullbackData B S hS).triangle
        ((overBaseChangeCone f).w ((schemesOverToOver Y).map g))) α :=
  PullbackData.relHomFunctor_map_op _ (smallEtaleDerivedPullbackData_isCoherent B S hS)
    (overBaseChangeCone f) K E _ α

/-- The degree-zero term of the Čech nerve of a morphism `q : V ⟶ T` of test schemes, over `Y`,
is `V`. -/
def testSchemeCechZeroIso {T V : SchemesOver Y} (q : V ⟶ T) :
    (schemesOverToOver Y).obj V ≅
      (augmentedOver (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).augmentedCechNerve
        T.hom).obj (Opposite.op ⦋0⦌) :=
  Over.isoMk (asIso (WidePullback.π (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left)
    0)).symm (by
      change inv (WidePullback.π (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) 0) ≫
        WidePullback.base (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) ≫ T.hom =
          V.hom
      rw [← WidePullback.π_arrow (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) 0,
        Category.assoc, IsIso.inv_hom_id_assoc]
      exact CostructuredArrow.w q)

/-- The degree-one term of the Čech nerve of a morphism `q : V ⟶ T` of test schemes, over `Y`,
is the fibre product `V ×_T V`, given by any cartesian square of the schemes of the site. -/
def testSchemeCechOneIso {T V O : SchemesOver Y} (q : V ⟶ T) (p₁ p₂ : O ⟶ V)
    (hO : IsPullback p₁.left p₂.left q.left q.left) :
    (schemesOverToOver Y).obj O ≅
      (augmentedOver (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).augmentedCechNerve
        T.hom).obj (Opposite.op ⦋1⦌) := by
  have hO' := isPullback_schemeSpaceFunctor_map hO
  let Q := (schemeSpaceFunctor B S hS).map q.left
  let e : (schemeSpaceFunctor B S hS).obj O.left ≅
      widePullback _ (fun _ : Fin 2 => (schemeSpaceFunctor B S hS).obj V.left) fun _ => Q :=
    { hom := WidePullback.lift ((schemeSpaceFunctor B S hS).map p₁.left ≫ Q)
        ![(schemeSpaceFunctor B S hS).map p₁.left, (schemeSpaceFunctor B S hS).map p₂.left]
        (fun j => by
          fin_cases j
          · rfl
          · exact hO'.w.symm)
      inv := hO'.lift (WidePullback.π (fun _ : Fin 2 => Q) 0)
        (WidePullback.π (fun _ : Fin 2 => Q) 1)
        (by rw [WidePullback.π_arrow, WidePullback.π_arrow])
      hom_inv_id := by
        apply hO'.hom_ext
        · rw [Category.assoc, IsPullback.lift_fst, WidePullback.lift_π, Category.id_comp]
          rfl
        · rw [Category.assoc, IsPullback.lift_snd, WidePullback.lift_π, Category.id_comp]
          rfl
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro j
          fin_cases j
          · rw [Category.assoc, WidePullback.lift_π, Category.id_comp]
            exact IsPullback.lift_fst _ _ _ _
          · rw [Category.assoc, WidePullback.lift_π, Category.id_comp]
            exact IsPullback.lift_snd _ _ _ _
        · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, IsPullback.lift_fst,
            Category.id_comp, WidePullback.π_arrow] }
  refine Over.isoMk e ?_
  change WidePullback.lift _ _ _ ≫ WidePullback.base (fun _ : Fin 2 => Q) ≫ T.hom = O.hom
  rw [WidePullback.lift_base_assoc, Category.assoc, CostructuredArrow.w q]
  exact CostructuredArrow.w p₁

/-- The degree-zero term of the Čech nerve maps to `T` by `q`. -/
theorem cechZeroIso_hom_comp_augmentedOverHom {T V : SchemesOver Y} (q : V ⟶ T) :
    (testSchemeCechZeroIso q).hom ≫ augmentedOverHom
        (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).augmentedCechNerve T.hom
        (Opposite.op ⦋0⦌) = (schemesOverToOver Y).map q := by
  refine Over.OverMorphism.ext ?_
  show inv (WidePullback.π (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) 0) ≫
    WidePullback.base (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) =
      (schemeSpaceFunctor B S hS).map q.left
  rw [← WidePullback.π_arrow (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) 0,
    IsIso.inv_hom_id_assoc]

/-- The two faces of the degree-one term of the Čech nerve are the two projections of
`V ×_T V`. -/
theorem cechOneIso_hom_comp_δ {T V O : SchemesOver Y} (q : V ⟶ T) (p₁ p₂ : O ⟶ V)
    (hO : IsPullback p₁.left p₂.left q.left q.left) (k : Fin 2) :
    (testSchemeCechOneIso q p₁ p₂ hO).hom ≫
        (augmentedOver (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).augmentedCechNerve
          T.hom).map (SimplexCategory.δ k).op ≫ (testSchemeCechZeroIso q).inv =
      (schemesOverToOver Y).map (![p₂, p₁] k) := by
  refine Over.OverMorphism.ext ?_
  show WidePullback.lift _ _ _ ≫ (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).cechNerve.map
    (SimplexCategory.δ k).op ≫
      WidePullback.π (fun _ : Fin 1 => (schemeSpaceFunctor B S hS).map q.left) 0 =
      (schemeSpaceFunctor B S hS).map (![p₂, p₁] k).left
  refine (congrArg (CategoryStruct.comp _) (WidePullback.lift_π _ _ _ _ _)).trans ?_
  refine (WidePullback.lift_π _ _ _ _ _).trans ?_
  fin_cases k <;> rfl

/-- The relative derived Hom functor on the test schemes is the relative derived Hom functor on
the algebraic spaces over `Y`, restricted. -/
theorem relativeDerivedHom_map_eq_over (K E : derivedModules B S hS X) {U T : SchemesOver Y}
    (g : U ⟶ T) (α : (relativeDerivedHom f K E).obj (Opposite.op T)) :
    (relativeDerivedHom f K E).map g.op α =
      (relativeDerivedHomOver f K E).map ((schemesOverToOver Y).map g).op α :=
  rfl

/-- **Descent of `T ↦ Hom(K_T, E_T)` along one fppf covering of test schemes** (Stacks 0DL9
applied to the Čech hypercovering `X_{V_•} ⟶ X_T`): for a morphism `q : V ⟶ T` of test schemes
which is an fppf covering and a cartesian square `O = V ×_T V`, a section over `V` whose two
restrictions to `O` agree is the restriction of exactly one section over `T`. -/
theorem relativeDerivedHom_single_descent (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    (K E : derivedModules B S hS X) {T V O : SchemesOver Y} (q : V ⟶ T)
    (hq : fppfCoveringMorphisms B S hS ((schemeSpaceFunctor B S hS).map q.left))
    (p₁ p₂ : O ⟶ V) (hO : IsPullback p₁.left p₂.left q.left q.left)
    (hKE : DescentHypotheses B S hS f K E ((schemesOverToOver Y).obj T))
    (ψ : (relativeDerivedHom f K E).obj (Opposite.op V)) :
    (relativeDerivedHom f K E).map p₁.op ψ = (relativeDerivedHom f K E).map p₂.op ψ ↔
      ∃! g : (relativeDerivedHom f K E).obj (Opposite.op T),
        (relativeDerivedHom f K E).map q.op g = ψ := by
  have hd := relativeDerivedHomOver_descent f h0DL9 ((schemeSpaceFunctor B S hS).map q.left)
    T.hom hq K E hKE ((relativeDerivedHomOver f K E).map (testSchemeCechZeroIso q).inv.op ψ)
  have hinj : ∀ {U U' : Over Y} (e : U ≅ U'),
      Function.Injective ((relativeDerivedHomOver f K E).map e.hom.op) := fun e =>
    Function.LeftInverse.injective (g := (relativeDerivedHomOver f K E).map e.inv.op) fun x =>
      FunctorToTypes.map_map_eq_self_of_comp_eq_id (relativeDerivedHomOver f K E)
        (by rw [← op_comp, e.inv_hom_id, op_id]) x
  have hface : ∀ k : Fin 2,
      (relativeDerivedHomOver f K E).map (testSchemeCechOneIso q p₁ p₂ hO).hom.op
      ((relativeDerivedHomOver f K E).map
        ((augmentedOver (Arrow.mk ((schemeSpaceFunctor B S hS).map q.left)).augmentedCechNerve
          T.hom).map (SimplexCategory.δ k).op).op
        ((relativeDerivedHomOver f K E).map (testSchemeCechZeroIso q).inv.op ψ)) =
      (relativeDerivedHom f K E).map (![p₂, p₁] k).op ψ := fun k =>
    FunctorToTypes.map_map_map_eq_of_comp_eq (relativeDerivedHomOver f K E) _ _ _ _
      (cechOneIso_hom_comp_δ q p₁ p₂ hO k) ψ
  refine Iff.trans (eq_comm.trans ((Eq.congr (hface 0) (hface 1)).symm.trans
    (hinj (testSchemeCechOneIso q p₁ p₂ hO)).eq_iff)) (hd.trans (existsUnique_congr fun g => ?_))
  exact FunctorToTypes.map_eq_map_inv_iff (relativeDerivedHomOver f K E)
    (testSchemeCechZeroIso q) _ _
    (cechZeroIso_hom_comp_augmentedOverHom q) g ψ

end SingleDescent

/-! ### The relative derived Hom functor on a disjoint union -/

section Pieces

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The relative derived Hom functor takes disjoint unions to products**, granted
`AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct`: for a test scheme `W` over `Y` with a
morphism `c` of its underlying scheme to a disjoint union `W₀ = ∐ W_k` of schemes of the site,
and test schemes `P_k ⟶ W` whose underlying squares over `W_k ⟶ W₀` are cartesian, a section
over `W` is a family of sections over the `P_k`. -/
theorem relativeDerivedHom_pieces_bijective (hD : DerivedHomDisjointUnionProduct B S hS)
    (K E : derivedModules B S hS X) {W : SchemesOver Y} {ι : Type u}
    (Wk : ι → BigFppfOver B S hS) (W₀ : BigFppfOver B S hS) (w : ∀ k, Wk k ⟶ W₀)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W₀)
      fun k => (BigFppfOver.toScheme B S hS).map (w k)))
    (c : W.left ⟶ W₀) (P' : ι → SchemesOver Y) (jk : ∀ k, P' k ⟶ W)
    (pk : ∀ k, (P' k).left ⟶ Wk k) (hsq : ∀ k, IsPullback (jk k).left (pk k) c (w k)) :
    Function.Bijective (fun α : (relativeDerivedHom f K E).obj (Opposite.op W) =>
      fun k => (relativeDerivedHom f K E).map (jk k).op α) := by
  have hb := hD Wk W₀ w hW (V := baseChangeSpace f W)
    (baseChangeInclusion f W ≫ (schemeSpaceFunctor B S hS).map c)
    (fun k => baseChangeSpace f (P' k))
    (fun k => (overBaseChangeFunctor f ⋙ Over.forget X).map ((schemesOverToOver Y).map (jk k)))
    (fun k => baseChangeInclusion f (P' k) ≫ (schemeSpaceFunctor B S hS).map (pk k))
    (fun k => (isPullback_baseChangeMap f (jk k)).paste_vert
      (isPullback_schemeSpaceFunctor_map (hsq k)))
    (((smallEtaleDerivedPullbackData B S hS).pull
      ((overBaseChangeCone f).leg ((schemesOverToOver Y).obj W))).obj K)
    (((smallEtaleDerivedPullbackData B S hS).pull
      ((overBaseChangeCone f).leg ((schemesOverToOver Y).obj W))).obj E)
  constructor
  · intro α β h
    refine hb.1 (funext fun k => ?_)
    exact (Functor.conjHom_inj_iff _ α β).1 ((relativeDerivedHom_map_eq f K E (jk k) α).symm.trans
      ((congrFun h k).trans (relativeDerivedHom_map_eq f K E (jk k) β)))
  · intro r
    obtain ⟨φ, hφ⟩ := hb.2 fun k =>
      (((smallEtaleDerivedPullbackData B S hS).triangle
        ((overBaseChangeCone f).w ((schemesOverToOver Y).map (jk k)))).inv.app K ≫ r k ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle
        ((overBaseChangeCone f).w ((schemesOverToOver Y).map (jk k)))).hom.app E)
    exact ⟨φ, funext fun k => (relativeDerivedHom_map_eq f K E (jk k) φ).trans
      (Functor.conjHom_eq_of_map_eq _ φ (r k) (congrFun hφ k))⟩

end Pieces

/-! ### The sheaf condition on test schemes -/

section Criterion

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

/-- **A covering sieve of the big fppf site of `S` is refined by a single surjective flat
morphism locally of finite presentation out of a disjoint union of members of the sieve**, the
disjoint union being a coproduct of the underlying schemes. This is
`AlgebraicGeometry.BigFppfOver.exists_flat_singleton_refinement_of_mem_topology`, with the
coproduct recorded on the underlying schemes. -/
theorem exists_flat_sigma_refinement_of_mem_topology (T : BigFppfOver B S hS) {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T) :
    ∃ (ι : Type u) (X : ι → BigFppfOver B S hS) (V : BigFppfOver B S hS)
      (j : ∀ i, X i ⟶ V) (q : V ⟶ T) (g : ∀ i, X i ⟶ T),
      (∀ i, R.arrows (g i)) ∧ (∀ i, j i ≫ q = g i) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
        fun i => (BigFppfOver.toScheme B S hS).map (j i))) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) := by
  classical
  choose X g hgR hgaff hgsize hgf hgp hgcov using
    fun x : (BigFppfOver.toScheme B S hS).obj T =>
      BigFppfOver.exists_affine_flat_mem_sieve_of_mem_topology B S hS hR x
  set μ : Cardinal.{u} := 2 ^ ((BigFppfOver.toScheme B S hS).obj T).size with hμdef
  have hμ : μ < B.cutoff := B.cutoff_isStrongPrelimit T.left.property
  have hι : Cardinal.mk ((BigFppfOver.toScheme B S hS).obj T : Type u) ≤ μ :=
    Scheme.mk_le_two_pow_size ((BigFppfOver.toScheme B S hS).obj T)
  have hXsize : ∀ x, ((BigFppfOver.toScheme B S hS).obj (X x)).size ≤ μ := fun x =>
    (hgsize x).trans (Cardinal.cantor _).le
  obtain ⟨V, j, hjopen, hjcov, ⟨hjS⟩, ⟨hjsite⟩, -⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hXsize
  let 𝒰 : ((BigFppfOver.toScheme B S hS).obj V).OpenCover.{u} :=
    { I₀ := _
      X := fun i => (BigFppfOver.toScheme B S hS).obj (X i)
      f := fun i => (BigFppfOver.toScheme B S hS).map (j i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hjcov, hjopen⟩ }
  have hfac : ∀ i, 𝒰.f i ≫ (BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hjsite g) =
      (BigFppfOver.toScheme B S hS).map (g i) := fun i =>
    ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.fac hjsite g i))
  refine ⟨_, X, V, j, Cofan.IsColimit.desc hjsite g, g, hgR,
    fun i => Cofan.IsColimit.fac hjsite g i, ⟨hjS⟩, ?_, ?_, ?_⟩
  · rw [surjective_iff]
    intro t
    obtain ⟨y, hy⟩ := hgcov t
    refine ⟨((BigFppfOver.toScheme B S hS).map (j t)) y, ?_⟩
    calc ((BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hjsite g))
          (((BigFppfOver.toScheme B S hS).map (j t)) y)
        = ((BigFppfOver.toScheme B S hS).map (j t) ≫
            (BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hjsite g)) y := rfl
      _ = ((BigFppfOver.toScheme B S hS).map (g t)) y := by rw [← hfac t]
      _ = t := hy
  · have : IsZariskiLocalAtSource (@Flat.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    rw [hfac i]
    exact hgf i
  · have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    rw [hfac i]
    exact hgp i

variable {Y : AlgebraicSpaces B S hS}

/-- The restriction of a test scheme `T` over `Y` along a morphism `h : Z ⟶ T` of the site:
the scheme `Z` with the structure morphism `Z ⟶ T ⟶ Y`. -/
abbrev restrictTest (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    SchemesOver Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map h ≫ T.hom)

/-- The morphism from the restriction of a test scheme to the test scheme. -/
abbrev restrictTestHom (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    restrictTest T h ⟶ T :=
  CostructuredArrow.homMk h rfl

/-- The morphism between two restrictions of a test scheme induced by a morphism `m` with
`m ≫ h = h'`. -/
abbrev restrictTestMap (T : SchemesOver Y) {Z Z' : BigFppfOver B S hS} {h : Z ⟶ T.left}
    {h' : Z' ⟶ T.left} (m : Z' ⟶ Z) (e : m ≫ h = h') : restrictTest T h' ⟶ restrictTest T h :=
  CostructuredArrow.homMk m (by
    subst e
    simp only [CostructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_comp,
      Category.assoc])

/-- The structure morphism of the test scheme of a restricted section. -/
theorem pointTestScheme_hom_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : Y.1.obj (Opposite.op T)) :
    (schemeSpaceFunctor B S hS).map g ≫ (pointTestScheme T y).hom =
      (pointTestScheme T' (Y.1.map g.op y)).hom :=
  CostructuredArrow.w (pointTestHom g rfl)

/-- The test schemes of two equal sections have the same structure morphism. -/
theorem pointTestScheme_hom_eq {Z : BigFppfOver B S hS} {y₁ y₂ : Y.1.obj (Opposite.op Z)}
    (e : y₁ = y₂) : (pointTestScheme Z y₁).hom = (pointTestScheme Z y₂).hom := by
  rw [e]

/-- The restriction of the test scheme of a section along `h` has the structure morphism of the
test scheme of the restricted section, as an identity of the underlying scheme. -/
theorem map_id_comp_pointTestScheme_hom {T Z : BigFppfOver B S hS} (h : Z ⟶ T)
    (y : Y.1.obj (Opposite.op T)) {a : Y.1.obj (Opposite.op Z)} (ha : Y.1.map h.op y = a) :
    (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫ (pointTestScheme Z a).hom =
      (restrictTest (pointTestScheme T y) h).hom := by
  subst ha
  refine (congrArg (· ≫ (pointTestScheme Z (Y.1.map h.op y)).hom)
    (CategoryTheory.Functor.map_id _ _)).trans ((Category.id_comp _).trans ?_)
  exact (pointTestScheme_hom_map h y).symm

/-- The test scheme of a restricted section has the structure morphism of the restriction of the
test scheme of the section, as an identity of the underlying scheme. -/
theorem map_id_comp_restrictTest_hom {T Z : BigFppfOver B S hS} (h : Z ⟶ T)
    (y : Y.1.obj (Opposite.op T)) :
    (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫ (restrictTest (pointTestScheme T y) h).hom =
      (pointTestScheme Z (Y.1.map h.op y)).hom := by
  refine (congrArg (· ≫ (restrictTest (pointTestScheme T y) h).hom)
    (CategoryTheory.Functor.map_id _ _)).trans ((Category.id_comp _).trans ?_)
  exact pointTestScheme_hom_map h y

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type w)

/-- Two restrictions of an element of a presheaf of sets compose to the restriction along the
composite. -/
private theorem map_op_map_op_of_comp_eq {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*) {a b c : C}
    {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) (x : F.obj (Opposite.op c)) :
    F.map f.op (F.map g.op x) = F.map k.op x := by
  subst h
  simp

/-- Restrictions of elements over the test schemes of two equal sections agree when the elements
are heterogeneously equal and the restriction morphisms have the same underlying morphism. -/
theorem map_eq_map_of_heq {Z : BigFppfOver B S hS} {y₁ y₂ : Y.1.obj (Opposite.op Z)}
    (e : y₁ = y₂) {b₁ : R.obj (Opposite.op (pointTestScheme Z y₁))}
    {b₂ : R.obj (Opposite.op (pointTestScheme Z y₂))} (hb : HEq b₁ b₂) {U : SchemesOver Y}
    (μ₁ : U ⟶ pointTestScheme Z y₁) (μ₂ : U ⟶ pointTestScheme Z y₂) (hμ : μ₁.left = μ₂.left) :
    R.map μ₁.op b₁ = R.map μ₂.op b₂ := by
  subst e
  obtain rfl := eq_of_heq hb
  rw [CostructuredArrow.hom_ext μ₁ μ₂ hμ]

/-- Two elements of the total presheaf agree when their sections agree and one element is the
restriction of the other along the identity of the underlying scheme. -/
theorem totalPresheaf_mk_eq_of_map {Z : BigFppfOver B S hS} {y₁ y₂ : Y.1.obj (Opposite.op Z)}
    (e : y₁ = y₂) (b₁ : R.obj (Opposite.op (pointTestScheme Z y₁)))
    (b₂ : R.obj (Opposite.op (pointTestScheme Z y₂)))
    (μ : pointTestScheme Z y₁ ⟶ pointTestScheme Z y₂)
    (hμ : μ.left = 𝟙 Z) (h : R.map μ.op b₂ = b₁) :
    (⟨y₁, b₁⟩ : Σ y : Y.1.obj (Opposite.op Z), R.obj (Opposite.op (pointTestScheme Z y))) =
      ⟨y₂, b₂⟩ := by
  subst e
  have hμ' : μ = 𝟙 _ := CostructuredArrow.hom_ext _ _ hμ
  subst hμ'
  rw [op_id, FunctorToTypes.map_id_apply] at h
  rw [h]

/-- **The fppf sheaf condition for a functor on the test schemes**, in terms of the test schemes:
`R` is an fppf sheaf over `Y` as soon as, for every test scheme `T` and every covering sieve of
its underlying scheme, a compatible family of elements over the restrictions of `T` has exactly
one amalgamation over `T`. -/
theorem isFppfSheafOver_of_amalgamation
    (H : ∀ (T : SchemesOver Y) (𝒮 : Sieve T.left), 𝒮 ∈ BigFppfOver.topology B S hS T.left →
      ∀ r : ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left), 𝒮.arrows h →
          R.obj (Opposite.op (restrictTest T h)),
      (∀ ⦃Z Z' : BigFppfOver B S hS⦄ (h : Z ⟶ T.left) (h' : Z' ⟶ T.left) (hh : 𝒮.arrows h)
          (hh' : 𝒮.arrows h') (m : Z' ⟶ Z) (e : m ≫ h = h'),
          R.map (restrictTestMap T m e).op (r h hh) = r h' hh') →
      ∃! g : R.obj (Opposite.op T), ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left)
        (hh : 𝒮.arrows h), R.map (restrictTestHom T h).op g = r h hh) :
    IsFppfSheafOver R := by
  unfold IsFppfSheafOver
  rw [isSheaf_iff_isSheaf_of_type]
  intro T₀ 𝒮 h𝒮 xf hx
  have hY : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).1 Y.2.isSheaf
  have hxs := hx.to_sieveCompatible
  -- the sections of `Y`
  let xY : Presieve.FamilyOfElements Y.1 𝒮.arrows := fun _ h hh => (xf h hh).1
  have hxY : xY.Compatible := fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w =>
    congrArg Sigma.fst (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨y, hy, -⟩ := hY 𝒮 h𝒮 xY hxY
  have hy' : ∀ ⦃Z⦄ (h : Z ⟶ T₀) (hh : 𝒮.arrows h), Y.1.map h.op y = (xf h hh).1 := hy
  let T := pointTestScheme T₀ y
  -- the identification of the restrictions of `T` with the test schemes of the sections
  have hε : ∀ ⦃Z⦄ (h : Z ⟶ T₀) (hh : 𝒮.arrows h),
      (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫ (pointTestScheme Z (xf h hh).1).hom =
        (restrictTest T h).hom := fun _ h hh => map_id_comp_pointTestScheme_hom h y (hy' h hh)
  let ε : ∀ ⦃Z⦄ (h : Z ⟶ T₀) (hh : 𝒮.arrows h),
      restrictTest T h ⟶ pointTestScheme Z (xf h hh).1 := fun Z h hh =>
    CostructuredArrow.homMk (𝟙 Z) (hε h hh)
  let r : ∀ ⦃Z⦄ (h : Z ⟶ T.left), 𝒮.arrows h → R.obj (Opposite.op (restrictTest T h)) :=
    fun Z h hh => R.map (ε h hh).op (xf h hh).2
  have hν : ∀ ⦃Z⦄ (h : Z ⟶ T₀),
      (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫ (restrictTest T h).hom =
        (pointTestScheme Z (Y.1.map h.op y)).hom := fun _ h => map_id_comp_restrictTest_hom h y
  let ν : ∀ ⦃Z⦄ (h : Z ⟶ T₀), pointTestScheme Z (Y.1.map h.op y) ⟶ restrictTest T h :=
    fun Z h => CostructuredArrow.homMk (𝟙 Z) (hν h)
  -- the second components of the family
  have hx₂ : ∀ ⦃Z Z'⦄ (h : Z ⟶ T₀) (hh : 𝒮.arrows h) (m : Z' ⟶ Z),
      HEq (xf (m ≫ h) (𝒮.downward_closed hh m)).2
        (R.map (pointTestHom m rfl).op (xf h hh).2) := fun Z Z' h hh m =>
    (Sigma.mk.inj_iff.1 ((hxs h m hh).trans (totalPresheaf_map_apply R m.op (xf h hh)))).2
  have hx₁ : ∀ ⦃Z Z'⦄ (h : Z ⟶ T₀) (hh : 𝒮.arrows h) (m : Z' ⟶ Z),
      (xf (m ≫ h) (𝒮.downward_closed hh m)).1 = Y.1.map m.op (xf h hh).1 := fun Z Z' h hh m =>
    (Sigma.mk.inj_iff.1 ((hxs h m hh).trans (totalPresheaf_map_apply R m.op (xf h hh)))).1
  have hr : ∀ ⦃Z Z' : BigFppfOver B S hS⦄ (h : Z ⟶ T.left) (h' : Z' ⟶ T.left)
      (hh : 𝒮.arrows h) (hh' : 𝒮.arrows h') (m : Z' ⟶ Z) (e : m ≫ h = h'),
      R.map (restrictTestMap T m e).op (r h hh) = r h' hh' := by
    intro Z Z' h h' hh hh' m e
    subst e
    show R.map _ (R.map _ _) = R.map _ _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have hμ : ∀ (μ : restrictTest T (m ≫ h) ⟶ pointTestScheme Z' (Y.1.map m.op (xf h hh).1)),
        μ.left = 𝟙 Z' → R.map (restrictTestMap T m rfl ≫ ε h hh).op (xf h hh).2 =
          R.map μ.op (R.map (pointTestHom m rfl).op (xf h hh).2) := fun μ hμ => by
      have e : restrictTestMap T m rfl ≫ ε h hh = μ ≫ pointTestHom m rfl :=
        CostructuredArrow.hom_ext _ _ (by
          show m ≫ 𝟙 Z = μ.left ≫ m
          rw [hμ]
          exact (Category.comp_id m).trans (Category.id_comp m).symm)
      rw [e, op_comp, FunctorToTypes.map_comp_apply]
    have hw : (schemeSpaceFunctor B S hS).map (𝟙 Z') ≫
        (pointTestScheme Z' (Y.1.map m.op (xf h hh).1)).hom = (restrictTest T (m ≫ h)).hom :=
      map_id_comp_pointTestScheme_hom (m ≫ h) y
        ((FunctorToTypes.map_comp_apply Y.1 h.op m.op y).trans
          (congrArg (Y.1.map m.op) (hy' h hh)))
    rw [hμ (CostructuredArrow.homMk (𝟙 Z') hw) rfl]
    exact (map_eq_map_of_heq R (hx₁ h hh m).symm (hx₂ h hh m).symm _ _ rfl)
  obtain ⟨g, hg, hgu⟩ := H T 𝒮 h𝒮 r hr
  refine ⟨⟨y, g⟩, fun Z h hh => ?_, fun z hz => ?_⟩
  · -- `⟨y, g⟩` is an amalgamation
    refine (totalPresheaf_map_apply R h.op ⟨y, g⟩).trans
      (totalPresheaf_mk_eq_of_map R (hy' h hh) _ _ (ν h ≫ ε h hh) (Category.id_comp _) ?_)
    rw [op_comp, FunctorToTypes.map_comp_apply]
    show R.map (ν h).op (r h hh) = _
    rw [← hg h hh, ← FunctorToTypes.map_comp_apply, ← op_comp]
    have e : ν h ≫ restrictTestHom T h = pointTestHom h rfl :=
      CostructuredArrow.hom_ext _ _ (Category.id_comp h)
    rw [e]
    rfl
  · -- uniqueness
    obtain ⟨y', g'⟩ := z
    have hzY : y' = y := (hY 𝒮 h𝒮).isSeparatedFor.ext fun Z h hh =>
      (congrArg Sigma.fst (hz h hh)).trans (hy' h hh).symm
    subst hzY
    have hg' : ∀ ⦃Z⦄ (h : Z ⟶ T.left) (hh : 𝒮.arrows h),
        R.map (restrictTestHom T h).op g' = r h hh := fun Z h hh => by
      have hz' := (totalPresheaf_map_apply R h.op ⟨y', g'⟩).symm.trans (hz h hh)
      have h₂ := (Sigma.mk.inj_iff.1 hz').2
      have hν' : (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫
          (pointTestScheme Z (Y.1.map h.op y')).hom = (restrictTest T h).hom :=
        map_id_comp_pointTestScheme_hom h y' rfl
      have h₃ := map_eq_map_of_heq R (Sigma.mk.inj_iff.1 hz').1 h₂
        (CostructuredArrow.homMk (𝟙 Z) hν') (ε h hh) rfl
      show _ = R.map (ε h hh).op (xf h hh).2
      have e : restrictTestHom T h = CostructuredArrow.homMk (𝟙 Z) hν' ≫ pointTestHom h rfl :=
        CostructuredArrow.hom_ext _ _ (Category.id_comp h).symm
      rw [← h₃, e]
      exact FunctorToTypes.map_comp_apply R _ _ g'
    rw [hgu g' hg']

/-- Restricting twice along restrictions of a test scheme is restricting along the composite. -/
theorem map_restrictTestMap_restrictTestMap {T : SchemesOver Y} {Z Z' Z'' : BigFppfOver B S hS}
    {h : Z ⟶ T.left} {h' : Z' ⟶ T.left} {h'' : Z'' ⟶ T.left} (m₂ : Z' ⟶ Z)
    (e₂ : m₂ ≫ h = h') (m₁ : Z'' ⟶ Z') (e₁ : m₁ ≫ h' = h'') (m : Z'' ⟶ Z) (e : m ≫ h = h'')
    (hm : m₁ ≫ m₂ = m) (x : R.obj (Opposite.op (restrictTest T h))) :
    R.map (restrictTestMap T m₁ e₁).op (R.map (restrictTestMap T m₂ e₂).op x) =
      R.map (restrictTestMap T m e).op x := by
  exact map_op_map_op_of_comp_eq R (CostructuredArrow.hom_ext _ _ hm) x

/-- Restricting a restriction from `T` is restricting from `T` along the composite. -/
theorem map_restrictTestMap_restrictTestHom {T : SchemesOver Y} {Z Z' : BigFppfOver B S hS}
    {h : Z ⟶ T.left} {h' : Z' ⟶ T.left} (m : Z' ⟶ Z) (e : m ≫ h = h')
    (x : R.obj (Opposite.op T)) :
    R.map (restrictTestMap T m e).op (R.map (restrictTestHom T h).op x) =
      R.map (restrictTestHom T h').op x := by
  exact map_op_map_op_of_comp_eq R (CostructuredArrow.hom_ext _ _ e) x

/-- The pullback condition of a fibre square of the site, for the restriction of a test scheme
along its first projection. -/
theorem pullback_snd_comp_eq {T : SchemesOver Y} {Z W : BigFppfOver B S hS} {h : Z ⟶ T.left}
    {q : W ⟶ Z} {h' : W ⟶ T.left} (e : q ≫ h = h') :
    pullback.snd q q ≫ h' = pullback.fst q q ≫ h' := by
  rw [← e, ← Category.assoc, ← pullback.condition, Category.assoc]

/-- A section restricted along the first projection of a fibre square of the site has equal
restrictions to the self-fibre product of that projection. -/
theorem map_restrictTestMap_pullback_fst_eq {T : SchemesOver Y} {Z W : BigFppfOver B S hS}
    (h : Z ⟶ T.left) (q : W ⟶ T.left) (x : R.obj (Opposite.op (restrictTest T h))) :
    R.map (restrictTestMap T (pullback.fst (pullback.fst h q) (pullback.fst h q)) rfl).op
        (R.map (restrictTestMap T (pullback.fst h q) rfl).op x) =
      R.map (restrictTestMap T (pullback.snd (pullback.fst h q) (pullback.fst h q))
        (pullback_snd_comp_eq rfl)).op
        (R.map (restrictTestMap T (pullback.fst h q) rfl).op x) := by
  rw [map_restrictTestMap_restrictTestMap R (pullback.fst h q) rfl _ rfl
      (pullback.fst (pullback.fst h q) (pullback.fst h q) ≫ pullback.fst h q)
      (Category.assoc _ _ _) rfl,
    map_restrictTestMap_restrictTestMap R (pullback.fst h q) rfl _ _
      (pullback.fst (pullback.fst h q) (pullback.fst h q) ≫ pullback.fst h q)
      (Category.assoc _ _ _) pullback.condition.symm]

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type w)

/-- **The fppf sheaf condition from the two inputs of step (S)**, for a functor `R` on the test
schemes over `Y`: if `R` takes disjoint unions of schemes of the site to products
(`HDinj`, `HDsurj`) and satisfies descent along one fppf covering, with the chosen fibre product
as overlap (`HS`), then `R` is an fppf sheaf over `Y`. -/
theorem isFppfSheafOver_of_descent
    (HDinj : ∀ (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) {ι : Type u}
      (Xk : ι → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ k, Xk k ⟶ V)
      (_ : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
        fun k => (BigFppfOver.toScheme B S hS).map (j k))) (c : Z ⟶ V),
      Function.Injective (fun α : R.obj (Opposite.op (restrictTest T h)) => fun k =>
        R.map (restrictTestMap T (pullback.fst c (j k)) rfl).op α))
    (HDsurj : ∀ (T : SchemesOver Y) {ι : Type u} (Xk : ι → BigFppfOver B S hS)
      (V : BigFppfOver B S hS) (j : ∀ k, Xk k ⟶ V)
      (_ : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
        fun k => (BigFppfOver.toScheme B S hS).map (j k))) (q : V ⟶ T.left)
      (g : ∀ k, Xk k ⟶ T.left) (hjq : ∀ k, j k ≫ q = g k),
      Function.Surjective (fun α : R.obj (Opposite.op (restrictTest T q)) => fun k =>
        R.map (restrictTestMap T (j k) (hjq k)).op α))
    (HS : ∀ (T : SchemesOver Y) {Z W : BigFppfOver B S hS} (h : Z ⟶ T.left) (q : W ⟶ Z)
      (h' : W ⟶ T.left) (e : q ≫ h = h'),
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Flat ((BigFppfOver.toScheme B S hS).map q) →
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) →
      ∀ ψ : R.obj (Opposite.op (restrictTest T h')),
        (R.map (restrictTestMap T (pullback.fst q q) rfl).op ψ =
          R.map (restrictTestMap T (pullback.snd q q) (pullback_snd_comp_eq e)).op ψ) ↔
        ∃! g : R.obj (Opposite.op (restrictTest T h)), R.map (restrictTestMap T q e).op g = ψ) :
    IsFppfSheafOver R := by
  refine isFppfSheafOver_of_amalgamation R fun T Sv hSv r hr => ?_
  obtain ⟨ι, Xk, V, j, q, g, hgS, hjq, ⟨hV⟩, hqs, hqf, hqp⟩ :=
    exists_flat_sigma_refinement_of_mem_topology T.left hSv
  -- the family as one section over `V`
  obtain ⟨ψ, hψ⟩ := HDsurj T Xk V j hV q g hjq fun k => r (g k) (hgS k)
  have hψk : ∀ k, R.map (restrictTestMap T (j k) (hjq k)).op ψ = r (g k) (hgS k) :=
    fun k => congrFun hψ k
  -- a restriction of `ψ` through a member of the disjoint union is the given section
  have hloc : ∀ {Z : BigFppfOver B S hS} (k : ι) (n : Z ⟶ Xk k) (m : Z ⟶ V)
      (_ : n ≫ j k = m) (h' : Z ⟶ T.left) (e : m ≫ q = h') (hh' : Sv.arrows h'),
      R.map (restrictTestMap T m e).op ψ = r h' hh' := by
    intro Z k n m hm h' e hh'
    have e' : n ≫ g k = h' := by rw [← hjq k, ← Category.assoc, hm, e]
    rw [← map_restrictTestMap_restrictTestMap R (j k) (hjq k) n e' m e hm ψ, hψk k]
    exact hr (g k) h' (hgS k) hh' n e'
  -- two restrictions through members of the disjoint union
  have hloc₂ : ∀ {Z Z' : BigFppfOver B S hS} {h₁ : Z' ⟶ T.left} (m₂ : Z' ⟶ V)
      (e₂ : m₂ ≫ q = h₁) (m₁ : Z ⟶ Z') (h' : Z ⟶ T.left) (e₁ : m₁ ≫ h₁ = h') (k : ι)
      (n : Z ⟶ Xk k) (hn : n ≫ j k = m₁ ≫ m₂),
      R.map (restrictTestMap T m₁ e₁).op (R.map (restrictTestMap T m₂ e₂).op ψ) =
        r h' (by rw [← e₁, ← e₂, ← Category.assoc, ← hn, Category.assoc, hjq k]
                 exact Sv.downward_closed (hgS k) n) := by
    intro Z Z' h₁ m₂ e₂ m₁ h' e₁ k n hn
    rw [map_restrictTestMap_restrictTestMap R m₂ e₂ m₁ e₁ (m₁ ≫ m₂)
      (by rw [Category.assoc, e₂, e₁]) rfl]
    exact hloc k n _ hn h' _ _
  -- the two restrictions of `ψ` to `V ×_T V` agree
  have heq : R.map (restrictTestMap T (pullback.fst q q) rfl).op ψ =
      R.map (restrictTestMap T (pullback.snd q q)
        (pullback_snd_comp_eq (Category.comp_id q))).op ψ := by
    refine HDinj T _ Xk V j hV (pullback.fst q q) (funext fun k => ?_)
    dsimp only
    refine HDinj T _ Xk V j hV (pullback.fst (pullback.fst q q) (j k) ≫ pullback.snd q q)
      (funext fun l => ?_)
    dsimp only
    rw [map_restrictTestMap_restrictTestMap R (pullback.fst q q) rfl
        (pullback.fst (pullback.fst q q) (j k)) rfl
        (pullback.fst (pullback.fst q q) (j k) ≫ pullback.fst q q) (Category.assoc _ _ _) rfl,
      map_restrictTestMap_restrictTestMap R (pullback.snd q q) _
        (pullback.fst (pullback.fst q q) (j k)) rfl
        (pullback.fst (pullback.fst q q) (j k) ≫ pullback.snd q q)
        (by rw [Category.assoc, ← pullback.condition]) rfl,
      hloc₂ _ _ _ _ rfl k
        (pullback.fst (pullback.fst (pullback.fst q q) (j k) ≫ pullback.snd q q) (j l) ≫
          pullback.snd (pullback.fst q q) (j k))
        (by rw [Category.assoc, ← pullback.condition]),
      hloc₂ _ _ _ _ rfl l
        (pullback.snd (pullback.fst (pullback.fst q q) (j k) ≫ pullback.snd q q) (j l))
        (by rw [← pullback.condition])]
  obtain ⟨g₀, hg₀, hg₀u⟩ :=
    (HS T (𝟙 T.left) q q (Category.comp_id q) hqs hqf hqp ψ).1 heq
  -- the descended section over `T`
  let ι₀ : T ⟶ restrictTest T (𝟙 T.left) := CostructuredArrow.homMk (𝟙 T.left) (by
    simp only [CostructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_id,
      Category.id_comp])
  have hgT : ∀ {Z : BigFppfOver B S hS} (h : Z ⟶ T.left),
      R.map (restrictTestHom T h).op (R.map ι₀.op g₀) =
        R.map (restrictTestMap T h (Category.comp_id h)).op g₀ := by
    intro Z h
    exact map_op_map_op_of_comp_eq R (CostructuredArrow.hom_ext _ _ (Category.comp_id h)) g₀
  refine ⟨R.map ι₀.op g₀, fun Z h hh => ?_, fun g' hg' => ?_⟩
  · -- it restricts to the given section on every member of the sieve
    rw [hgT h]
    have sqS := (IsPullback.of_hasPullback h q).map (BigFppfOver.toScheme B S hS)
    have hqh := HS T h (pullback.fst h q) (pullback.fst h q ≫ h) rfl
      (MorphismProperty.of_isPullback sqS.flip hqs) (MorphismProperty.of_isPullback sqS.flip hqf)
      (MorphismProperty.of_isPullback sqS.flip hqp)
      (R.map (restrictTestMap T (pullback.fst h q) rfl).op
        (R.map (restrictTestMap T h (Category.comp_id h)).op g₀))
    have hpieces : R.map (restrictTestMap T (pullback.fst h q) rfl).op
          (R.map (restrictTestMap T h (Category.comp_id h)).op g₀) =
        R.map (restrictTestMap T (pullback.fst h q) rfl).op (r h hh) := by
      refine HDinj T _ Xk V j hV (pullback.snd h q) (funext fun k => ?_)
      dsimp only
      rw [map_restrictTestMap_restrictTestMap R h (Category.comp_id h) (pullback.fst h q) rfl
          (pullback.fst h q ≫ h) (Category.comp_id _) rfl,
        map_restrictTestMap_restrictTestMap R _ _ (pullback.fst (pullback.snd h q) (j k)) rfl
          (pullback.fst (pullback.snd h q) (j k) ≫ pullback.fst h q ≫ h) (Category.comp_id _) rfl,
        ← map_restrictTestMap_restrictTestMap R q (Category.comp_id q)
          (pullback.fst (pullback.snd h q) (j k) ≫ pullback.snd h q)
          (by rw [Category.assoc, ← pullback.condition])
          (pullback.fst (pullback.snd h q) (j k) ≫ pullback.fst h q ≫ h) (Category.comp_id _)
          (by rw [Category.assoc, ← pullback.condition]),
        hg₀, hloc k (pullback.snd (pullback.snd h q) (j k)) _ pullback.condition.symm _ _
          (by simpa [Category.assoc] using (Sv.downward_closed hh
            (pullback.fst (pullback.snd h q) (j k) ≫ pullback.fst h q))),
        map_restrictTestMap_restrictTestMap R (pullback.fst h q) rfl
          (pullback.fst (pullback.snd h q) (j k)) rfl
          (pullback.fst (pullback.snd h q) (j k) ≫ pullback.fst h q) (Category.assoc _ _ _) rfl,
        hr h _ hh _ _ (Category.assoc _ _ _)]
    exact (hqh.1 (map_restrictTestMap_pullback_fst_eq R h q _)).unique rfl hpieces.symm
  · -- uniqueness
    have hι : ι₀ ≫ restrictTestHom T (𝟙 T.left) = 𝟙 _ :=
      CostructuredArrow.hom_ext _ _ (Category.comp_id _)
    have hg'0 : R.map ι₀.op (R.map (restrictTestHom T (𝟙 T.left)).op g') = g' :=
      FunctorToTypes.map_map_eq_self_of_comp_eq_id R (by rw [← op_comp, hι, op_id]) g'
    rw [← hg'0]
    congr 1
    refine hg₀u _ ?_
    beta_reduce
    rw [map_restrictTestMap_restrictTestHom R q (Category.comp_id q)]
    refine HDinj T _ Xk V j hV (𝟙 V) (funext fun k => ?_)
    dsimp only
    rw [map_restrictTestMap_restrictTestHom R _ rfl,
      hg' _ (by
        rw [show pullback.fst (𝟙 V) (j k) = pullback.snd (𝟙 V) (j k) ≫ j k by
          rw [← pullback.condition, Category.comp_id], Category.assoc, hjq k]
        exact Sv.downward_closed (hgS k) _),
      hloc k (pullback.snd (𝟙 V) (j k)) _ (by rw [← pullback.condition, Category.comp_id]) _ rfl]

end Criterion

/-! ### Step (S) -/

section StepS

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

/-- **Step (S) of the proof of Stacks 0DLC, part (3), granted the derived Hom of a disjoint
union** (`AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct`): Stacks 0DL9 makes
`T ↦ Hom(K_T, E_T)` an fppf sheaf over `Y` when the negative extensions of `K_V`, `E_V` vanish
for every `V` over `Y`.

A covering sieve of a test scheme `T` is refined by one fppf covering `q : V ⟶ T` out of a
disjoint union `V = ∐ X_k` of members of the sieve
(`AlgebraicGeometry.Space.exists_flat_sigma_refinement_of_mem_topology`).  A compatible family
is a section over `V` by the disjoint union property
(`AlgebraicGeometry.Space.relativeDerivedHom_pieces_bijective`), whose two restrictions to
`V ×_T V` agree because they agree on its pieces `X_k ×_T X_l`; Stacks 0DL9 along the Čech
hypercovering of `X_V ⟶ X_T` (`AlgebraicGeometry.Space.relativeDerivedHom_single_descent`)
descends it to `T`, and the same two inputs show that the descended section restricts to the
given family on every member of the sieve, and that it is unique. -/
theorem relativeDerivedHomIsSheafOfDescent_of_disjointUnion
    (hD : DerivedHomDisjointUnionProduct B S hS) : RelativeDerivedHomIsSheafOfDescent B S hS := by
  intro h0DL9 X Y f K E hK hE hneg
  have hKE : ∀ W : SchemesOver Y,
      DescentHypotheses B S hS f K E ((schemesOverToOver Y).obj W) := by
    intro W
    have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS f
      ((schemesOverToOver Y).obj W).hom
    have hrep : yoneda.relativelyRepresentable
        (overProjection f ((schemesOverToOver Y).obj W)).hom :=
      (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS hsq).flip
        (relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 W.hom.hom)
    exact ⟨isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS _ hrep K hK,
      isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS _ hrep E hE, hneg⟩
  have hfppf : ∀ {U W : BigFppfOver B S hS} (q : U ⟶ W),
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Flat ((BigFppfOver.toScheme B S hS).map q) →
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) →
      fppfCoveringMorphisms B S hS ((schemeSpaceFunctor B S hS).map q) :=
    fun {U W} q hs hf hp =>
      isFppfCovering_yoneda_map.{u, 0} B S hS (U := W) (fun _ : Unit => U) (fun _ => q)
        (fun _ => hf) (fun _ => hp) fun x => by
          obtain ⟨y, hy⟩ := hs.surj x
          exact ⟨(), y, hy⟩
  refine isFppfSheafOver_of_descent _ (fun T Z h ι Xk V j hV c => ?_)
    (fun T ι Xk V j hV q g hjq => ?_) (fun T Z W h q h' e hs hf hp ψ => ?_)
  · exact (relativeDerivedHom_pieces_bijective f hD K E Xk V j hV c
      (fun k => restrictTest T (pullback.fst c (j k) ≫ h))
      (fun k => restrictTestMap T (pullback.fst c (j k)) rfl) (fun k => pullback.snd c (j k))
      (fun k => by
        show IsPullback (pullback.fst c (j k)) _ _ _
        exact IsPullback.of_hasPullback c (j k))).1
  · exact (relativeDerivedHom_pieces_bijective f hD K E Xk V j hV (𝟙 V)
      (fun k => restrictTest T (g k)) (fun k => restrictTestMap T (j k) (hjq k))
      (fun k => 𝟙 _) (fun k => by
        show IsPullback (j k) (𝟙 _) (𝟙 V) (j k)
        exact IsPullback.id_vert (j k))).2
  · exact relativeDerivedHom_single_descent f h0DL9 K E (restrictTestMap T q e)
      (hfppf q hs hf hp) _ _ (IsPullback.of_hasPullback q q) (hKE _) ψ

end StepS

end AlgebraicGeometry.Space

end
