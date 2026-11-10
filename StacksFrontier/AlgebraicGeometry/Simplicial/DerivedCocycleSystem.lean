module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair

/-!
# Cartesian simplicial systems of the derived category from a cocycle isomorphism (Stacks 0GME)

Let `S` be a simplicial-site situation (Stacks 09WE). An object `K₀` of the derived category of
abelian sheaves on its degree-zero component, together with an isomorphism
`α : f_{δ¹₁}⁻¹K₀ ≅ f_{δ¹₀}⁻¹K₀` on the degree-one component satisfying the cocycle condition on
the degree-two component, determines the cartesian simplicial system of Stacks 0D9G whose object
in degree `n` is `f_{τⁿₙ}⁻¹K₀`, the inverse image of `K₀` along the last vertex of `⦋n⦌`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.DerivedCocyclePair`: the pair `(K₀, α)` with its
  cocycle condition, the input data of Stacks 0GME.
* `CategoryTheory.SimplicialSiteSituation.pairDerivedSystem`: **Stacks 0GME**, the simplicial
  system of the derived category it determines, with `pairDerivedSystem_obj` its object in each
  degree.
* `CategoryTheory.SimplicialSiteSituation.derivedEdgeTransport`: the comparison between the
  inverse images of `K₀` along two vertices of `⦋n⦌` joined by an edge, obtained from `α`.
* `CategoryTheory.SimplicialSiteSituation.zeroDerivedCocyclePair`: the pair on a zero object,
  whose comparison and cocycle condition are forced.

## Main results

* `CategoryTheory.SimplicialSiteSituation.pairDerivedSystem_cartesian`: **Stacks 0GME**, the
  system is cartesian.
* `CategoryTheory.derivedCompIso_pentagon` and `CategoryTheory.derivedCompIso_unit_right`: the
  cocycle and unit laws for the derived compositor of Stacks 0D9G, deduced from the
  corresponding laws of the exact functors it localizes.
* `CategoryTheory.SimplicialSiteSituation.derivedInverseImageCompIso_assoc_app` and
  `.derivedInverseImageCompIso_comp_id`: those two laws for the derived inverse images of `S`.
* `CategoryTheory.SimplicialDerivedSystem.Cartesian.map_id`: in a cartesian simplicial system of
  Stacks 0D9G the transition along an identity is the unit comparison, by the right unit law.
* `CategoryTheory.SimplicialSiteSituation.derivedEdgeTransport_comp`: the comparisons attached
  to the edges of a simplex compose; this is the content of the cocycle condition.

## Implementation notes

The construction follows Stacks 0D7I for sheaves of sets, which the library has in
`StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair`: a pair `(K₀, α)` assigns to every
pair of vertices `i ≤ j` of `⦋n⦌` a comparison `derivedEdgeTransport` between the inverse images
of `K₀` along them, obtained by pulling `α` back along the edge joining them; the cocycle
condition says exactly that these comparisons compose, and the transition of the system at
`φ : m ⟶ n` pulls back to the image of the last vertex of `⦋m⦌` and then transports along the
edge from there to the last vertex of `⦋n⦌`.

What has to be supplied here is the pseudofunctoriality of the *derived* inverse images, which
Stacks 0D9G provides as data — the compositor `derivedInverseImageCompIso` and the unit
`derivedInverseImageIdIso` — but not as laws. `derivedCompIso_pentagon` and
`derivedCompIso_unit_right` prove the two laws for an arbitrary exact-functor compositor from
the corresponding laws of the abelian functors, by `CategoryTheory.Localization.natTrans_ext`
and the formulas for the comparisons on the image of a complex. The abelian laws in turn come
from the laws of Stacks 09WF for sheaves of sets, `canonicalCompositionComparison_assoc` and
`_comp_id`, because `sheafCompose _ (forget Ab)` is faithful and carries the abelian
comparisons to the comparisons of sheaves of sets.

*No transport occurs in the cocycle law.* Composition in the simplex category is associative by
`rfl`, so `derivedInverseImage S ((χ ≫ ψ) ≫ φ)` and `derivedInverseImage S (χ ≫ ψ ≫ φ)` are the
same functor and the two sides of `derivedInverseImageCompIso_assoc_app` have the same type as
written. The unit law does need a transport, since `φ ≫ 𝟙 n = φ` is not `rfl`; it is carried as
a transport of *objects*, as in Stacks 0D7I.

*The two developments are not shared.* The simplicial combinatorics below duplicates that of
Stacks 0D7I for sheaves of sets. Sharing them would need the inverse images to be packaged as a
pseudofunctor out of the simplex category; the library packages the sheaf-of-sets inverse images
that way, in `componentPseudofunctor`, but not the derived ones, and the comparisons of Stacks
0D9G are not of that shape.

Statements mixing the two spellings of a triple composite are type-correct only at default
transparency, so `rw` cannot be used on them; `faithful_comp_ext` and `faithful_comp_eq` take
the images of the factors as hypotheses so that the mixed spellings are resolved by
`exact`-level unification only.

## References

* [Stacks Project, Tag 0GME](https://stacks.math.columbia.edu/tag/0GME)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites
open scoped Simplicial ZeroObject

namespace CategoryTheory

/-! ### Reflecting a factorization along a faithful functor -/

/-- A faithful functor reflects an equality between two factorizations of a morphism, given the
images of the four factors. -/
theorem faithful_comp_ext {C : Type*} [Category C] {D : Type*} [Category D] (Φ : C ⥤ D)
    [Φ.Faithful] {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ W) (f' : X ⟶ Z) (g' : Z ⟶ W)
    {a : Φ.obj X ⟶ Φ.obj Y} {b : Φ.obj Y ⟶ Φ.obj W} {c : Φ.obj X ⟶ Φ.obj Z}
    {d : Φ.obj Z ⟶ Φ.obj W}
    (ha : Φ.map f = a) (hb : Φ.map g = b) (hc : Φ.map f' = c) (hd : Φ.map g' = d)
    (h : a ≫ b = c ≫ d) : f ≫ g = f' ≫ g' :=
  Φ.map_injective (by rw [Φ.map_comp, Φ.map_comp, ha, hb, hc, hd]; exact h)

/-- A faithful functor reflects an equality between a factorization of a morphism and the
morphism itself, given the images of the three maps involved. -/
theorem faithful_comp_eq {C : Type*} [Category C] {D : Type*} [Category D] (Φ : C ⥤ D)
    [Φ.Faithful] {X Y W : C} (f : X ⟶ Y) (g : Y ⟶ W) (k : X ⟶ W)
    {a : Φ.obj X ⟶ Φ.obj Y} {b : Φ.obj Y ⟶ Φ.obj W} {c : Φ.obj X ⟶ Φ.obj W}
    (ha : Φ.map f = a) (hb : Φ.map g = b) (hc : Φ.map k = c)
    (h : a ≫ b = c) : f ≫ g = k :=
  Φ.map_injective (by rw [Φ.map_comp, ha, hb, hc]; exact h)

/-- Inverting an equality between two composites of isomorphisms. -/
private theorem inv_comp_inv_eq_of_hom_comp_eq {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : X ≅ W) (d : W ≅ Z) (h : a.hom ≫ b.hom = c.hom ≫ d.hom) :
    b.inv ≫ a.inv = d.inv ≫ c.inv :=
  congrArg Iso.inv (Iso.ext h : a ≪≫ b = c ≪≫ d)

/-! ### The two coherence laws for the derived compositor of Stacks 0D9G -/

section Pentagon

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (K : C ⥤ D) (FG : A ⥤ C) (GK : B ⥤ D) (H : A ⥤ D)
  [F.Additive] [G.Additive] [K.Additive] [FG.Additive] [GK.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits GK] [PreservesFiniteColimits GK]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The cocycle law for the derived compositor.** Four exact functors with compositors
satisfying the cocycle law have derived compositors satisfying it. -/
theorem derivedCompIso_pentagon
    (efg : FG ≅ F ⋙ G) (egk : GK ≅ G ⋙ K) (e₁ : H ≅ FG ⋙ K) (e₂ : H ≅ F ⋙ GK)
    (h : ∀ X : A, e₁.hom.app X ≫ K.map (efg.hom.app X) =
      e₂.hom.app X ≫ egk.hom.app (F.obj X)) :
    (derivedCompIso FG K H e₁).hom ≫
        Functor.whiskerRight (derivedCompIso F G FG efg).hom K.mapDerivedCategory =
      (derivedCompIso F GK H e₂).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (derivedCompIso G K GK egk).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X ↦ ?_
  have hnat : GK.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) ≫
        (derivedCompIso G K GK egk).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
      (derivedCompIso G K GK egk).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
        K.mapDerivedCategory.map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X)) :=
    (derivedCompIso G K GK egk).hom.naturality (F.mapDerivedCategoryFactors.inv.app X)
  have hnatK : K.mapDerivedCategoryFactors.inv.app
          ((FG.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        K.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex efg (ComplexShape.up ℤ)).hom.app X)) =
      DerivedCategory.Q.map ((K.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex efg (ComplexShape.up ℤ)).hom.app X)) ≫
        K.mapDerivedCategoryFactors.inv.app
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
    (K.mapDerivedCategoryFactors.inv.naturality
      ((NatIso.mapHomologicalComplex efg (ComplexShape.up ℤ)).hom.app X)).symm
  have hcx : (NatIso.mapHomologicalComplex e₁ (ComplexShape.up ℤ)).hom.app X ≫
        (K.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex efg (ComplexShape.up ℤ)).hom.app X) =
      (NatIso.mapHomologicalComplex e₂ (ComplexShape.up ℤ)).hom.app X ≫
        (NatIso.mapHomologicalComplex egk (ComplexShape.up ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
    HomologicalComplex.hom_ext _ _ fun i ↦ h (X.X i)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [derivedCompIso_hom_app_Q, derivedCompIso_hom_app_Q, derivedCompIso_hom_app_Q]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc K.mapDerivedCategory, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_obj]
  rw [hnat, derivedCompIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hnatK, ← Functor.map_comp_assoc DerivedCategory.Q,
    ← Functor.map_comp_assoc DerivedCategory.Q, hcx]
  rfl

end Pentagon

section Unit

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]
  (F : A ⥤ B) (U : B ⥤ B) (H : A ⥤ B) [F.Additive] [U.Additive] [H.Additive]

/-- A unit law for a compositor of additive functors holds termwise on cochain complexes. -/
theorem mapHomologicalComplex_app_unit_right (cmp : H ≅ F ⋙ U) (uid : U ≅ 𝟭 B) (t : H ⟶ F)
    (h : ∀ Y : A, cmp.hom.app Y ≫ uid.hom.app (F.obj Y) = t.app Y)
    (X : CochainComplex A ℤ) :
    (NatIso.mapHomologicalComplex cmp (ComplexShape.up ℤ)).hom.app X ≫
        (NatIso.mapHomologicalComplex uid (ComplexShape.up ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) =
      (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app X :=
  HomologicalComplex.hom_ext _ _ fun i ↦ by simpa using h (X.X i)

end Unit

section DerivedUnit

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) (U : B ⥤ B) (H : A ⥤ B) [F.Additive] [U.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The right unit law for the derived compositor.** A compositor `H ≅ F ⋙ U` whose composite
with a unit comparison for `U` is a given transformation `t` has a derived compositor whose
composite with the derived unit comparison is the derived transformation of `t`. -/
theorem derivedCompIso_unit_right (cmp : H ≅ F ⋙ U) (uid : U ≅ 𝟭 B) (t : H ⟶ F)
    (tD : H.mapDerivedCategory ⟶ F.mapDerivedCategory)
    (htD : ∀ X : CochainComplex A ℤ,
      tD.app (DerivedCategory.Q.obj X) ≫ F.mapDerivedCategoryFactors.hom.app X =
        H.mapDerivedCategoryFactors.hom.app X ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app X))
    (h : ∀ X : A, cmp.hom.app X ≫ uid.hom.app (F.obj X) = t.app X) :
    (derivedCompIso F U H cmp).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (derivedNatIso U (𝟭 B) uid ≪≫ derivedIdIso).hom = tD := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X ↦ ?_
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app X)).1
  have hnat : U.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) ≫
        (derivedNatIso U (𝟭 B) uid ≪≫ derivedIdIso).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
      (derivedNatIso U (𝟭 B) uid ≪≫ derivedIdIso).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
        F.mapDerivedCategoryFactors.inv.app X :=
    (derivedNatIso U (𝟭 B) uid ≪≫ derivedIdIso).hom.naturality
      (F.mapDerivedCategoryFactors.inv.app X)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [htD X, derivedCompIso_hom_app_Q]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app]
  rw [derivedNatIso_hom_app_Q, derivedIdIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.comp_obj, Category.comp_id, ← Functor.map_comp]
  rw [mapHomologicalComplex_app_unit_right F U H cmp uid t h X]

end DerivedUnit

namespace SimplicialSiteSituation

universe u v

variable (S : SimplicialSiteSituation.{u})

/-! ### The two coherence laws on sheaves of sets and on abelian sheaves -/

/-- The cocycle law for the inverse-image compositors of Stacks 09WF, read on an object and in
the direction of the compositors themselves. -/
theorem canonicalCompositionComparison_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n) (F : Sheaf (S.componentTopology k) (Type u)) :
    (canonicalCompositionComparison S χ (ψ ≫ φ)).hom.app F ≫
        (canonicalCompositionComparison S ψ φ).hom.app
          ((S.transitionMorphism χ).inverseImage.obj F) =
      (canonicalCompositionComparison S (χ ≫ ψ) φ).hom.app F ≫
        (S.transitionMorphism φ).inverseImage.map
          ((canonicalCompositionComparison S χ ψ).hom.app F) := by
  exact inv_comp_inv_eq_of_hom_comp_eq
    (S.pasteIso ψ φ ((S.transitionMorphism χ).inverseImage.obj F)) (S.pasteIso χ (ψ ≫ φ) F)
    ((S.transitionMorphism φ).inverseImage.mapIso (S.pasteIso χ ψ F)) (S.pasteIso (χ ≫ ψ) φ F)
    ((S.pasteIso_assoc χ ψ φ F).trans
      (congrArg (fun g => (S.transitionMorphism φ).inverseImage.map (S.pasteIso χ ψ F).hom ≫ g)
        (Category.comp_id (S.pasteIso (χ ≫ ψ) φ F).hom)))

/-- The right unit law for the inverse-image compositors of Stacks 09WF, read on an object: the
compositor at `φ ≫ 𝟙` followed by the unit comparison is the transport of objects. -/
theorem canonicalCompositionComparison_comp_id_app {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (canonicalCompositionComparison S φ (𝟙 n)).hom.app F ≫
        (canonicalIdentityComparison S n).hom.app
          ((S.transitionMorphism φ).inverseImage.obj F) =
      eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F)
        (Category.comp_id φ)) := by
  have h := S.pasteIsoOfEq_comp_id φ F
  rw [pasteIsoOfEq, Iso.trans_hom, eqToIso.hom, pasteIso, Iso.symm_hom] at h
  rw [← h, ← Category.assoc]
  simp

/-- The cocycle law for the abelian inverse-image compositors of Stacks 0D9G, read on an
object. -/
theorem abelianCompIso_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m)
    (φ : m ⟶ n) (X : Sheaf (S.componentTopology k) Ab.{u}) :
    (abelianCompIso S χ (ψ ≫ φ)).hom.app X ≫
        (abelianCompIso S ψ φ).hom.app ((abelianTransition S χ).obj X) =
      (abelianCompIso S (χ ≫ ψ) φ).hom.app X ≫
        (abelianTransition S φ).map ((abelianCompIso S χ ψ).hom.app X) :=
  faithful_comp_ext (sheafCompose (S.componentTopology n) (forget Ab.{u})) _ _ _ _
    (forget_map_abelianCompIso_app S χ (ψ ≫ φ) X)
    (forget_map_abelianCompIso_app S ψ φ _)
    (forget_map_abelianCompIso_app S (χ ≫ ψ) φ X)
    ((rfl : (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransition S φ).map ((abelianCompIso S χ ψ).hom.app X)) =
      (S.transitionMorphism φ).inverseImage.map
        ((sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          ((abelianCompIso S χ ψ).hom.app X))).trans
      (congrArg (S.transitionMorphism φ).inverseImage.map
        (forget_map_abelianCompIso_app S χ ψ X)))
    (S.canonicalCompositionComparison_assoc_app χ ψ φ _)

/-- The underlying map of sheaves of sets of a transport of abelian transitions along an
equality of simplex maps is the transport of their inverse images. -/
theorem forget_map_eqToHom_abelianTransition {m n : SimplexCategory} (k k' : m ⟶ n)
    (hk : k = k') (X : Sheaf (S.componentTopology m) Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((eqToHom (congrArg (fun j => abelianTransition S j) hk)).app X) =
      eqToHom (congrArg (fun j => (S.transitionMorphism j).inverseImage.obj
        ((sheafCompose (S.componentTopology m) (forget Ab.{u})).obj X)) hk) := by
  subst hk
  change (sheafCompose (S.componentTopology n) (forget Ab.{u})).map (𝟙 _) = 𝟙 _
  exact (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_id _

/-- The right unit law for the abelian inverse-image compositors of Stacks 0D9G, read on an
object. -/
theorem abelianCompIso_comp_id_app {m n : SimplexCategory} (φ : m ⟶ n)
    (X : Sheaf (S.componentTopology m) Ab.{u}) :
    (abelianCompIso S φ (𝟙 n)).hom.app X ≫
        (abelianIdIso S n).hom.app ((abelianTransition S φ).obj X) =
      (eqToHom (congrArg (fun k => abelianTransition S k) (Category.comp_id φ))).app X :=
  faithful_comp_eq (sheafCompose (S.componentTopology n) (forget Ab.{u})) _ _ _
    (forget_map_abelianCompIso_app S φ (𝟙 n) X)
    (forget_map_abelianIdIso_app S n _)
    (S.forget_map_eqToHom_abelianTransition _ _ (Category.comp_id φ) X)
    (S.canonicalCompositionComparison_comp_id_app φ _)

/-! ### The two coherence laws on derived categories -/

variable [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- A transport of derived inverse images along an equality of simplex maps is, on the image of
a complex, the localization of the corresponding transport of abelian transitions. -/
theorem eqToHom_derivedInverseImage_app_Q {m n : SimplexCategory} (k k' : m ⟶ n) (hk : k = k')
    (X : CochainComplex (Sheaf (S.componentTopology m) Ab.{u}) ℤ) :
    (eqToHom (congrArg (fun j => derivedInverseImage S j) hk)).app
          (DerivedCategory.Q.obj X) ≫
        (abelianTransition S k').mapDerivedCategoryFactors.hom.app X =
      (abelianTransition S k).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (eqToHom (congrArg (fun j => abelianTransition S j) hk))
          (ComplexShape.up ℤ)).app X) := by
  subst hk
  change 𝟙 ((DerivedCategory.Q ⋙
          (abelianTransition S k).mapDerivedCategory).obj X) ≫
        (abelianTransition S k).mapDerivedCategoryFactors.hom.app X =
      (abelianTransition S k).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (𝟙 (abelianTransition S k)) (ComplexShape.up ℤ)).app X)
  simp

/-- The cocycle law for the derived inverse-image compositors of Stacks 0D9G, read on an
object. No transport occurs: composition of simplex maps is associative by `rfl`. -/
theorem derivedInverseImageCompIso_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : DerivedCategory (Sheaf (S.componentTopology k) Ab.{u})) :
    (derivedInverseImageCompIso S χ (ψ ≫ φ)).hom.app X ≫
        (derivedInverseImageCompIso S ψ φ).hom.app ((derivedInverseImage S χ).obj X) =
      (derivedInverseImageCompIso S (χ ≫ ψ) φ).hom.app X ≫
        (derivedInverseImage S φ).map ((derivedInverseImageCompIso S χ ψ).hom.app X) :=
  (NatTrans.congr_app (derivedCompIso_pentagon (abelianTransition S χ)
    (abelianTransition S ψ) (abelianTransition S φ) (abelianTransition S (χ ≫ ψ))
    (abelianTransition S (ψ ≫ φ)) (abelianTransition S (χ ≫ ψ ≫ φ))
    (abelianCompIso S χ ψ) (abelianCompIso S ψ φ) (abelianCompIso S (χ ≫ ψ) φ)
    (abelianCompIso S χ (ψ ≫ φ))
    (fun Y => (S.abelianCompIso_assoc_app χ ψ φ Y).symm)) X).symm

/-- The right unit law for the derived inverse-image compositors of Stacks 0D9G. -/
theorem derivedInverseImageCompIso_comp_id {m n : SimplexCategory} (φ : m ⟶ n) :
    (derivedInverseImageCompIso S φ (𝟙 n)).hom ≫
        Functor.whiskerLeft (derivedInverseImage S φ)
          (derivedInverseImageIdIso S n).hom =
      eqToHom (congrArg (fun k => derivedInverseImage S k) (Category.comp_id φ)) :=
  derivedCompIso_unit_right (abelianTransition S φ) (abelianTransition S (𝟙 n))
    (abelianTransition S (φ ≫ 𝟙 n)) (abelianCompIso S φ (𝟙 n)) (abelianIdIso S n)
    (eqToHom (congrArg (fun k => abelianTransition S k) (Category.comp_id φ)))
    (eqToHom (congrArg (fun k => derivedInverseImage S k) (Category.comp_id φ)))
    (fun X => S.eqToHom_derivedInverseImage_app_Q _ _ (Category.comp_id φ) X)
    (fun Y => S.abelianCompIso_comp_id_app φ Y)

variable {S} in
/-- The transition of a simplicial system along a simplex map is determined, up to transport,
by the simplex map: equal simplex maps have transitions differing by the transport of derived
inverse images. -/
theorem _root_.CategoryTheory.SimplicialDerivedSystem.map_eq_of_eq
    (K : SimplicialDerivedSystem S) {m n : SimplexCategory} {k k' : m ⟶ n} (hk : k = k') :
    K.map k = (eqToHom (congrArg (fun j => derivedInverseImage S j) hk)).app (K.obj m) ≫
      K.map k' := by
  subst hk
  simp

variable {S} in
/-- A simplicial system whose transition along `𝟙 n` is invertible has that transition equal to
the unit comparison `f_{id}⁻¹ ≅ id`: the cocycle condition at `(𝟙 n, 𝟙 n)` makes the transition
an idempotent up to the compositor, and the right unit law identifies the compositor with the
inverse of the unit. -/
theorem _root_.CategoryTheory.SimplicialDerivedSystem.map_id_of_isIso
    (K : SimplicialDerivedSystem S) (n : SimplexCategory) [IsIso (K.map (𝟙 n))] :
    K.map (𝟙 n) = (derivedInverseImageIdIso S n).hom.app (K.obj n) := by
  have hcomp := K.map_comp (𝟙 n) (𝟙 n)
  rw [K.map_eq_of_eq (Category.comp_id (𝟙 n)), ← Category.assoc, cancel_mono] at hcomp
  have hunit := NatTrans.congr_app (S.derivedInverseImageCompIso_comp_id (𝟙 n)) (K.obj n)
  rw [NatTrans.comp_app, Functor.whiskerLeft_app] at hunit
  have hnat := (derivedInverseImageIdIso S n).hom.naturality (K.map (𝟙 n))
  rw [Functor.id_map] at hnat
  refine (cancel_epi ((eqToHom (congrArg (fun j => derivedInverseImage S j)
    (Category.comp_id (𝟙 n)))).app (K.obj n))).1 ?_
  conv_lhs => rw [← hunit]
  rw [Category.assoc, ← hnat, ← Category.assoc, ← hcomp]

variable {S} in
/-- In a cartesian simplicial system the transition along `𝟙 n` is the unit comparison
`f_{id}⁻¹ ≅ id`. -/
theorem _root_.CategoryTheory.SimplicialDerivedSystem.Cartesian.map_id
    {K : SimplicialDerivedSystem S} (hK : K.Cartesian) (n : SimplexCategory) :
    K.map (𝟙 n) = (derivedInverseImageIdIso S n).hom.app (K.obj n) := by
  have := hK (𝟙 n)
  exact K.map_id_of_isIso n

/-! ### The derived inverse-image compositor as an identification of objects -/

/-- The canonical identification `f_φ⁻¹f_ψ⁻¹K ≅ f_{ψ ≫ φ}⁻¹K` given by the derived
inverse-image compositor of Stacks 0D9G. -/
def derivedPasteIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    (derivedInverseImage S φ).obj ((derivedInverseImage S ψ).obj K) ≅
      (derivedInverseImage S (ψ ≫ φ)).obj K :=
  ((derivedInverseImageCompIso S ψ φ).app K).symm

/-- The derived compositor is natural in the object. -/
theorem derivedPasteIso_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    {K L : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})} (f : K ⟶ L) :
    (derivedInverseImage S φ).map ((derivedInverseImage S ψ).map f) ≫
          (S.derivedPasteIso ψ φ L).hom =
      (S.derivedPasteIso ψ φ K).hom ≫ (derivedInverseImage S (ψ ≫ φ)).map f := by
  simpa [derivedPasteIso] using (derivedInverseImageCompIso S ψ φ).inv.naturality f

/-- The cocycle law for the derived compositor, read on an object. -/
theorem derivedPasteIso_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (S.componentTopology k) Ab.{u})) :
    (S.derivedPasteIso ψ φ ((derivedInverseImage S χ).obj K)).hom ≫
        (S.derivedPasteIso χ (ψ ≫ φ) K).hom =
      (derivedInverseImage S φ).map (S.derivedPasteIso χ ψ K).hom ≫
        (S.derivedPasteIso (χ ≫ ψ) φ K).hom := by
  exact inv_comp_inv_eq_of_hom_comp_eq ((derivedInverseImageCompIso S χ (ψ ≫ φ)).app K)
    ((derivedInverseImageCompIso S ψ φ).app ((derivedInverseImage S χ).obj K))
    ((derivedInverseImageCompIso S (χ ≫ ψ) φ).app K)
    ((derivedInverseImage S φ).mapIso ((derivedInverseImageCompIso S χ ψ).app K))
    (S.derivedInverseImageCompIso_assoc_app χ ψ φ K)

/-- The derived compositor, written at a chosen factorization of a simplex map. -/
def derivedPasteIsoOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    (derivedInverseImage S φ).obj ((derivedInverseImage S ψ).obj K) ≅
      (derivedInverseImage S θ).obj K :=
  S.derivedPasteIso ψ φ K ≪≫
    eqToIso (congrArg (fun k => (derivedInverseImage S k).obj K) h)

/-- The derived compositor at a factorization is natural in the object. -/
theorem derivedPasteIsoOfEq_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (θ : l ⟶ n) (h : ψ ≫ φ = θ)
    {K L : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})} (f : K ⟶ L) :
    (derivedInverseImage S φ).map ((derivedInverseImage S ψ).map f) ≫
          (S.derivedPasteIsoOfEq ψ φ θ h L).hom =
      (S.derivedPasteIsoOfEq ψ φ θ h K).hom ≫ (derivedInverseImage S θ).map f := by
  subst h
  simpa [derivedPasteIsoOfEq] using S.derivedPasteIso_naturality ψ φ f

/-- At the tautological factorization the derived compositor is the derived compositor. -/
theorem derivedPasteIsoOfEq_rfl {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    S.derivedPasteIsoOfEq ψ φ (ψ ≫ φ) rfl K = S.derivedPasteIso ψ φ K := by
  apply Iso.ext
  simp [derivedPasteIsoOfEq]

/-- The cocycle law for the derived compositor at factorizations. -/
theorem derivedPasteIsoOfEq_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m)
    (φ : m ⟶ n) (χψ : k ⟶ m) (ψφ : l ⟶ n) (χψφ : k ⟶ n) (h₁ : χ ≫ ψ = χψ)
    (h₂ : ψ ≫ φ = ψφ) (h₃ : χψ ≫ φ = χψφ) (h₄ : χ ≫ ψφ = χψφ)
    (K : DerivedCategory (Sheaf (S.componentTopology k) Ab.{u})) :
    (derivedInverseImage S φ).map (S.derivedPasteIsoOfEq χ ψ χψ h₁ K).hom ≫
        (S.derivedPasteIsoOfEq χψ φ χψφ h₃ K).hom =
      (S.derivedPasteIsoOfEq ψ φ ψφ h₂ ((derivedInverseImage S χ).obj K)).hom ≫
        (S.derivedPasteIsoOfEq χ ψφ χψφ h₄ K).hom := by
  subst h₁
  subst h₂
  subst h₃
  simp only [derivedPasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  exact (S.derivedPasteIso_assoc χ ψ φ K).symm.trans
    (congrArg (fun g => (S.derivedPasteIso ψ φ ((derivedInverseImage S χ).obj K)).hom ≫ g)
      (Category.comp_id (S.derivedPasteIso χ (ψ ≫ φ) K).hom).symm)

/-- The right unit law: the derived compositor at `φ ≫ 𝟙` is the derived unit comparison. -/
theorem derivedPasteIsoOfEq_comp_id {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (S.componentTopology m) Ab.{u})) :
    (S.derivedPasteIsoOfEq φ (𝟙 n) φ (Category.comp_id φ) K).hom =
      (derivedInverseImageIdIso S n).hom.app ((derivedInverseImage S φ).obj K) := by
  have h := NatTrans.congr_app (S.derivedInverseImageCompIso_comp_id φ) K
  rw [eqToHom_app] at h
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [derivedPasteIsoOfEq, Iso.trans_hom, eqToIso.hom, derivedPasteIso, Iso.symm_hom, ← h,
    ← Category.assoc]
  simp

/-- The identification of the derived inverse images of an object along two factorizations
`ψ ≫ φ` and `ψ' ≫ φ'` of one simplex map. -/
def derivedGlueOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    (derivedInverseImage S φ).obj ((derivedInverseImage S ψ).obj K) ≅
      (derivedInverseImage S φ').obj ((derivedInverseImage S ψ').obj K) :=
  S.derivedPasteIsoOfEq ψ φ v h K ≪≫ (S.derivedPasteIsoOfEq ψ' φ' v h' K).symm

/-- The identification of two factorizations, written out. -/
theorem derivedGlueOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    (S.derivedGlueOfEq ψ ψ' φ φ' v h h' K).hom =
      (S.derivedPasteIsoOfEq ψ φ v h K).hom ≫ (S.derivedPasteIsoOfEq ψ' φ' v h' K).inv := rfl

/-- The inverse of the identification of two factorizations, written out. -/
theorem derivedGlueOfEq_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})) :
    (S.derivedGlueOfEq ψ ψ' φ φ' v h h' K).inv =
      (S.derivedPasteIsoOfEq ψ' φ' v h' K).hom ≫ (S.derivedPasteIsoOfEq ψ φ v h K).inv := rfl

/-- The identification of the two derived inverse images of `f_{δ¹₁}⁻¹K` to degree two occurring
in the cocycle condition, along `δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`. -/
def derivedGlueLeft (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S (SimplexCategory.δ (2 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K) ≅
      (derivedInverseImage S (SimplexCategory.δ (1 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K) :=
  S.derivedGlueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one K

/-- The identification of `f_{δ²₂}⁻¹f_{δ¹₀}⁻¹K` with `f_{δ²₀}⁻¹f_{δ¹₁}⁻¹K`, along
`δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀`. -/
def derivedGlueMiddle (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S (SimplexCategory.δ (2 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K) ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K) :=
  S.derivedGlueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero K

/-- The identification of the two derived inverse images of `f_{δ¹₀}⁻¹K` to degree two occurring
in the cocycle condition, along `δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`. -/
def derivedGlueRight (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S (SimplexCategory.δ (0 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K) ≅
      (derivedInverseImage S (SimplexCategory.δ (1 : Fin 3))).obj
        ((derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K) :=
  S.derivedGlueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one K

/-! ### The pair `(K₀, α)` -/

/-- **Stacks 0GME.** A pair `(K₀, α)`: an object of the derived category of abelian sheaves on
the degree-zero component of a simplicial-site situation together with an isomorphism
`α : f_{δ¹₁}⁻¹K₀ ≅ f_{δ¹₀}⁻¹K₀` on the degree-one component satisfying the cocycle condition
`f_{δ²₁}⁻¹α = f_{δ²₀}⁻¹α ∘ f_{δ²₂}⁻¹α` on the degree-two component. -/
structure DerivedCocyclePair (S : SimplicialSiteSituation.{u})
    [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})] where
  /-- The object of the derived category on the degree-zero component. -/
  obj : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})
  /-- The comparison isomorphism between the two derived inverse images to degree one. -/
  iso : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj obj ≅
    (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj obj
  /-- The cocycle condition on the degree-two component. -/
  cocycle :
    (derivedInverseImage S (SimplexCategory.δ (1 : Fin 3))).map iso.hom =
      (S.derivedGlueLeft obj).inv ≫
        (derivedInverseImage S (SimplexCategory.δ (2 : Fin 3))).map iso.hom ≫
        (S.derivedGlueMiddle obj).hom ≫
        (derivedInverseImage S (SimplexCategory.δ (0 : Fin 3))).map iso.hom ≫
        (S.derivedGlueRight obj).hom

/-- Derived inverse image is additive, being triangulated. Named because the instance for
`Functor.mapDerivedCategory` is not found through the definition of `derivedInverseImage`. -/
instance derivedInverseImage_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (derivedInverseImage S φ).Additive :=
  inferInstanceAs (abelianTransition S φ).mapDerivedCategory.Additive

/-- The pair on a zero object: the derived inverse images of a zero object are zero, so the
comparison is the unique one and the cocycle condition is automatic. -/
def zeroDerivedCocyclePair : DerivedCocyclePair S where
  obj := 0
  iso := (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).mapZeroObject ≪≫
    (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).mapZeroObject.symm
  cocycle := by
    refine ((isZero_zero _).of_iso ?_).eq_of_src _ _
    exact (derivedInverseImage S (SimplexCategory.δ (1 : Fin 3))).mapIso
        ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).mapZeroObject) ≪≫
      (derivedInverseImage S (SimplexCategory.δ (1 : Fin 3))).mapZeroObject

/-! ### Transport along the edges of a simplex -/

/-- The comparison between the derived inverse images of `K` along the two ends of an edge `φ`
of a simplex, obtained from the derived inverse image of `α` along `φ`. -/
def derivedTransportAlongIso (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (derivedInverseImage S v).obj K ≅ (derivedInverseImage S w).obj K :=
  (S.derivedPasteIsoOfEq _ φ v h₁ K).symm ≪≫
    (derivedInverseImage S φ).mapIso α ≪≫ S.derivedPasteIsoOfEq _ φ w h₀ K

/-- Transport along an edge, as a morphism. -/
def derivedTransportAlong (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (derivedInverseImage S v).obj K ⟶ (derivedInverseImage S w).obj K :=
  (S.derivedTransportAlongIso K α φ v w h₁ h₀).hom

/-- Transport along an edge is invertible. -/
instance derivedTransportAlong_isIso
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    IsIso (S.derivedTransportAlong K α φ v w h₁ h₀) :=
  inferInstanceAs (IsIso (S.derivedTransportAlongIso K α φ v w h₁ h₀).hom)

/-- The comparison between the derived inverse images of `K` along two vertices `i ≤ j` of
`⦋n⦌`, obtained from the derived inverse image of `α` along the edge joining them. -/
def derivedEdgeTransportIso (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj K ≅
      (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj K :=
  S.derivedTransportAlongIso K α (SimplexCategory.mkOfLe i j h) _ _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h)
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h)

/-- Transport along an edge of `⦋n⦌`, as a morphism. -/
def derivedEdgeTransport (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj K ⟶
      (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj K :=
  (S.derivedEdgeTransportIso K α i j h).hom

/-- Transport along an edge of `⦋n⦌` is invertible. -/
instance derivedEdgeTransport_isIso
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : IsIso (S.derivedEdgeTransport K α i j h) :=
  inferInstanceAs (IsIso (S.derivedEdgeTransportIso K α i j h).hom)

/-- Transport along an edge, written out. -/
theorem derivedTransportAlong_eq
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    S.derivedTransportAlong K α φ v w h₁ h₀ =
      (S.derivedPasteIsoOfEq _ φ v h₁ K).inv ≫ (derivedInverseImage S φ).map α.hom ≫
        (S.derivedPasteIsoOfEq _ φ w h₀ K).hom := rfl

/-- Transport along an edge of `⦋n⦌`, written out. -/
theorem derivedEdgeTransport_eq
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    S.derivedEdgeTransport K α i j h =
      (S.derivedPasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) K).inv ≫
        (derivedInverseImage S (SimplexCategory.mkOfLe i j h)).map α.hom ≫
        (S.derivedPasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) K).hom := rfl

/-- The identification of the derived inverse image of `K` along a vertex of `⦋m⦌`, pulled back
along a simplex map, with the inverse image along the image vertex. -/
def derivedVertexPaste {m n : SimplexCategory} (φ : m ⟶ n) (i : Fin (m.len + 1))
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S φ).obj
        ((derivedInverseImage S
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)).obj K) ≅
      (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len)
          (φ.toOrderHom i))).obj K :=
  S.derivedPasteIsoOfEq _ φ _ (SimplexCategory.vertexMap_comp φ i) K

/-- The vertex identifications are compatible with composition of simplex maps. -/
theorem derivedVertexPaste_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : Fin (l.len + 1)) (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S φ).map (S.derivedVertexPaste ψ i K).hom ≫
        (S.derivedVertexPaste φ (ψ.toOrderHom i) K).hom =
      (S.derivedPasteIso ψ φ
          ((derivedInverseImage S (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk l.len) i)).obj K)).hom ≫
        (S.derivedVertexPaste (ψ ≫ φ) i K).hom := by
  have h := S.derivedPasteIsoOfEq_assoc
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk l.len) i) ψ φ _ (ψ ≫ φ) _
    (SimplexCategory.vertexMap_comp ψ i) rfl
    (SimplexCategory.vertexMap_comp φ (ψ.toOrderHom i))
    (SimplexCategory.vertexMap_comp (ψ ≫ φ) i) K
  rw [S.derivedPasteIsoOfEq_rfl ψ φ] at h
  exact h

/-- Pulling back the source identification of an edge of `⦋m⦌` along a simplex map gives the
source identification of the image edge. -/
theorem derivedEdgePaste_one_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S φ).map
          (S.derivedPasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.mkOfLe i j h) _
            (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) K).hom ≫
        (S.derivedVertexPaste φ i K).hom =
      (S.derivedPasteIsoOfEq (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h)
            ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K)).hom ≫
        (S.derivedPasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) K).hom :=
  S.derivedPasteIsoOfEq_assoc (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom i))
    (SimplexCategory.delta_one_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ i)
    (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) K

/-- Pulling back the target identification of an edge of `⦋m⦌` along a simplex map gives the
target identification of the image edge. -/
theorem derivedEdgePaste_zero_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u})) :
    (derivedInverseImage S φ).map
          (S.derivedPasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.mkOfLe i j h) _
            (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h) K).hom ≫
        (S.derivedVertexPaste φ j K).hom =
      (S.derivedPasteIsoOfEq (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h)
            ((derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)).hom ≫
        (S.derivedPasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) K).hom :=
  S.derivedPasteIsoOfEq_assoc (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) j)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom j))
    (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ j)
    (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) K

/-- Composing edge transport with the source identification of the edge strips the
identification: what remains is the derived inverse image of `α` along the edge. -/
theorem derivedPasteIsoOfEq_comp_edgeTransport
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedPasteIsoOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) K).hom ≫
        S.derivedEdgeTransport K α i j h =
      (derivedInverseImage S (SimplexCategory.mkOfLe i j h)).map α.hom ≫
        (S.derivedPasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) K).hom := by
  rw [S.derivedEdgeTransport_eq K α i j h]
  simp

/-- Edge transport is compatible with pulling back along a simplex map. -/
theorem derivedEdgeTransport_map {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (derivedInverseImage S φ).map (S.derivedEdgeTransport K α i j h) ≫
        (S.derivedVertexPaste φ j K).hom =
      (S.derivedVertexPaste φ i K).hom ≫
        S.derivedEdgeTransport K α (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h) := by
  refine (cancel_epi ((derivedInverseImage S φ).map
    (S.derivedPasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
      (SimplexCategory.mkOfLe i j h) _
      (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) K).hom)).mp ?_
  calc _ = (S.derivedPasteIsoOfEq (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h)
            ((derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K)).hom ≫
        (derivedInverseImage S (SimplexCategory.mkOfLe (φ.toOrderHom i)
              (φ.toOrderHom j) (SimplexCategory.hom_le φ h))).map α.hom ≫
          (S.derivedPasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
              (SimplexCategory.hom_le φ h)) _
            (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
              (SimplexCategory.hom_le φ h)) K).hom := by
        rw [← Category.assoc _ ((derivedInverseImage S φ).map
            (S.derivedEdgeTransport K α i j h)), ← Functor.map_comp,
          S.derivedPasteIsoOfEq_comp_edgeTransport K α i j h, Functor.map_comp, Category.assoc,
          S.derivedEdgePaste_zero_comp φ i j h K, ← Category.assoc,
          S.derivedPasteIsoOfEq_naturality (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h) α.hom, Category.assoc]
    _ = _ := Eq.symm <| by
        rw [← Category.assoc, S.derivedEdgePaste_one_comp φ i j h K, Category.assoc,
          S.derivedPasteIsoOfEq_comp_edgeTransport K α (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)]

/-- Edge transport read along any presentation of the edge as a simplex map. -/
theorem derivedEdgeTransport_eq_transportAlong
    (K : DerivedCategory (Sheaf (S.componentTopology ⦋0⦌) Ab.{u}))
    (α : (derivedInverseImage S (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (derivedInverseImage S (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) (φ : ⦋1⦌ ⟶ ⦋n⦌)
    (hφ : SimplexCategory.mkOfLe i j h = φ)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j) :
    S.derivedEdgeTransport K α i j h = S.derivedTransportAlong K α φ _ _ h₁ h₀ := by
  subst hφ
  rfl

/-- The cocycle condition of a pair, read as composability of the transports along the three
edges of `⦋2⦌`. -/
theorem derivedEdgeTransport_cocycle_two (P : DerivedCocyclePair S) :
    S.derivedEdgeTransport P.obj P.iso (0 : Fin 3) 2 (by decide) =
      S.derivedEdgeTransport P.obj P.iso (0 : Fin 3) 1 (by decide) ≫
        S.derivedEdgeTransport P.obj P.iso (1 : Fin 3) 2 (by decide) := by
  rw [S.derivedEdgeTransport_eq_transportAlong (n := 2) P.obj P.iso 0 2 (by decide)
      (SimplexCategory.δ (1 : Fin 3)) (SimplexCategory.edgeMap_two_zero_two_eq _)
      SimplexCategory.delta_one_comp_delta_one SimplexCategory.delta_zero_comp_delta_one,
    S.derivedEdgeTransport_eq_transportAlong (n := 2) P.obj P.iso 0 1 (by decide)
      (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.edgeMap_two_zero_one_eq _)
      SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_zero_comp_delta_two,
    S.derivedEdgeTransport_eq_transportAlong (n := 2) P.obj P.iso 1 2 (by decide)
      (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.edgeMap_two_one_two_eq _)
      SimplexCategory.delta_one_comp_delta_zero SimplexCategory.delta_zero_comp_delta_zero]
  simp only [S.derivedTransportAlong_eq]
  rw [P.cocycle]
  simp only [derivedGlueLeft, derivedGlueMiddle, derivedGlueRight, S.derivedGlueOfEq_hom,
    S.derivedGlueOfEq_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Edge transports compose. -/
theorem derivedEdgeTransport_comp (P : DerivedCocyclePair S) {n : ℕ} (i j k : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    S.derivedEdgeTransport P.obj P.iso i k (hij.trans hjk) =
      S.derivedEdgeTransport P.obj P.iso i j hij ≫
        S.derivedEdgeTransport P.obj P.iso j k hjk := by
  have h := congrArg
    (fun t => (derivedInverseImage S
          (SimplexCategory.mkOfLeComp i j k hij hjk)).map t ≫
        (S.derivedVertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 2 P.obj).hom)
    (S.derivedEdgeTransport_cocycle_two P)
  simp only [Functor.map_comp, Category.assoc] at h
  rw [S.derivedEdgeTransport_map, S.derivedEdgeTransport_map, ← Category.assoc,
    S.derivedEdgeTransport_map, Category.assoc] at h
  exact (cancel_epi
    (S.derivedVertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 0 P.obj).hom).mp h

/-- Edge transport along a degenerate edge is the identity. -/
theorem derivedEdgeTransport_self (P : DerivedCocyclePair S) {n : ℕ} (i : Fin (n + 1)) :
    S.derivedEdgeTransport P.obj P.iso i i le_rfl = 𝟙 _ := by
  refine (cancel_epi (S.derivedEdgeTransport P.obj P.iso i i le_rfl)).mp ?_
  simpa using (S.derivedEdgeTransport_comp P i i i le_rfl le_rfl).symm

/-! ### The simplicial system attached to a pair -/

/-- The object in degree `n` of the system attached to a pair: the derived inverse image of its
degree-zero object along the last vertex of `⦋n⦌`. -/
def pairDerivedObj (P : DerivedCocyclePair S) (n : SimplexCategory) :
    DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  (derivedInverseImage S
    (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).obj P.obj

/-- The transition in the system attached to a pair, as an isomorphism: pull back to the image
of the last vertex and transport along the edge to the last vertex. -/
def pairDerivedTransitionIso (P : DerivedCocyclePair S) {m n : SimplexCategory} (φ : m ⟶ n) :
    (derivedInverseImage S φ).obj (S.pairDerivedObj P m) ≅ S.pairDerivedObj P n :=
  S.derivedVertexPaste φ (Fin.last m.len) P.obj ≪≫
    S.derivedEdgeTransportIso P.obj P.iso (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _)

/-- The transition in the system attached to a pair. -/
def pairDerivedTransition (P : DerivedCocyclePair S) {m n : SimplexCategory} (φ : m ⟶ n) :
    (derivedInverseImage S φ).obj (S.pairDerivedObj P m) ⟶ S.pairDerivedObj P n :=
  (S.pairDerivedTransitionIso P φ).hom

/-- The transitions of the system attached to a pair are invertible. -/
instance pairDerivedTransition_isIso (P : DerivedCocyclePair S) {m n : SimplexCategory}
    (φ : m ⟶ n) : IsIso (S.pairDerivedTransition P φ) :=
  inferInstanceAs (IsIso (S.pairDerivedTransitionIso P φ).hom)

/-- The transitions of the system attached to a pair are compatible with composition. -/
theorem pairDerivedTransition_comp (P : DerivedCocyclePair S) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.derivedPasteIso ψ φ (S.pairDerivedObj P l)).hom ≫ S.pairDerivedTransition P (ψ ≫ φ) =
      (derivedInverseImage S φ).map (S.pairDerivedTransition P ψ) ≫
        S.pairDerivedTransition P φ := by
  have hL : (S.derivedPasteIso ψ φ (S.pairDerivedObj P l)).hom ≫
        S.pairDerivedTransition P (ψ ≫ φ) =
      (S.derivedPasteIso ψ φ ((derivedInverseImage S
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk l.len)
              (Fin.last l.len))).obj P.obj)).hom ≫
        (S.derivedVertexPaste (ψ ≫ φ) (Fin.last l.len) P.obj).hom ≫
        S.derivedEdgeTransport P.obj P.iso
          (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len))) (Fin.last n.len)
          (Fin.le_last _) := rfl
  have hR : (derivedInverseImage S φ).map (S.pairDerivedTransition P ψ) ≫
        S.pairDerivedTransition P φ =
      (derivedInverseImage S φ).map
          ((S.derivedVertexPaste ψ (Fin.last l.len) P.obj).hom ≫
            S.derivedEdgeTransport P.obj P.iso (ψ.toOrderHom (Fin.last l.len))
              (Fin.last m.len) (Fin.le_last _)) ≫
        (S.derivedVertexPaste φ (Fin.last m.len) P.obj).hom ≫
        S.derivedEdgeTransport P.obj P.iso (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
          (Fin.le_last _) := rfl
  rw [hL, hR, Functor.map_comp, Category.assoc,
    reassoc_of% (S.derivedEdgeTransport_map φ P.obj P.iso (ψ.toOrderHom (Fin.last l.len))
      (Fin.last m.len) (Fin.le_last _)),
    ← S.derivedEdgeTransport_comp P, ← Category.assoc, S.derivedVertexPaste_comp ψ φ]
  exact (Category.assoc _ _ _).symm

/-- The transition at an identity simplex map is the derived unit comparison. -/
theorem pairDerivedTransition_id (P : DerivedCocyclePair S) (n : SimplexCategory) :
    S.pairDerivedTransition P (𝟙 n) =
      (derivedInverseImageIdIso S n).hom.app (S.pairDerivedObj P n) := by
  have h : S.pairDerivedTransition P (𝟙 n) =
      (S.derivedPasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))
          (𝟙 n) (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))
          (Category.comp_id _) P.obj).hom ≫
        S.derivedEdgeTransport P.obj P.iso (Fin.last n.len) (Fin.last n.len) le_rfl := rfl
  rw [h, S.derivedEdgeTransport_self P, Category.comp_id, S.derivedPasteIsoOfEq_comp_id]
  rfl

/-- **Stacks 0GME.** The cartesian simplicial system of the derived category attached to a pair
`(K₀, α)`: in degree `n` the derived inverse image of `K₀` along the last vertex of `⦋n⦌`. -/
@[stacks 0GME "the simplicial system"]
def pairDerivedSystem (P : DerivedCocyclePair S) : SimplicialDerivedSystem S where
  obj n := S.pairDerivedObj P n
  map φ := S.pairDerivedTransition P φ
  map_comp ψ φ :=
    (Iso.inv_comp_eq ((derivedInverseImageCompIso S ψ φ).app (S.pairDerivedObj P _))).mp
      (S.pairDerivedTransition_comp P ψ φ)

/-- **Stacks 0GME.** The object of the system in degree `n` is `f_{τⁿₙ}⁻¹K₀`, the derived
inverse image of `K₀` along the last vertex of `⦋n⦌`. -/
@[stacks 0GME "the objects of the system"]
theorem pairDerivedSystem_obj (P : DerivedCocyclePair S) (n : SimplexCategory) :
    (S.pairDerivedSystem P).obj n =
      (derivedInverseImage S
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).obj P.obj := rfl

/-- **Stacks 0GME.** The system attached to a pair is cartesian. -/
@[stacks 0GME "the system is cartesian"]
theorem pairDerivedSystem_cartesian (P : DerivedCocyclePair S) :
    (S.pairDerivedSystem P).Cartesian :=
  fun φ => S.pairDerivedTransition_isIso P φ

end SimplicialSiteSituation

end CategoryTheory

end
