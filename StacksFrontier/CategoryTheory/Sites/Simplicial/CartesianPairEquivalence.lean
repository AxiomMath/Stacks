module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairFunctor

/-!
# Cartesian sheaves of sets on a simplicial site are pairs with a cocycle isomorphism

Let `S` be a simplicial-site situation. A pair `(ℱ, α)` as in
`CategoryTheory.SimplicialSiteSituation.CartesianPair` determines a simplicial system of sheaves
on the components of `S`: in degree `n` the inverse image of `ℱ` along the last vertex of `⦋n⦌`,
with transitions assembled from the inverse images of `α` along the edges of `⦋n⦌`. The descent
construction of Stacks 09WF turns that system into a sheaf on the total site, which is cartesian
because the transitions are invertible, and whose associated pair is the given one. With the full
faithfulness of `CategoryTheory.SimplicialSiteSituation.cartesianPairFunctor` this gives the
equivalence of Stacks 0D7I for sheaves of sets.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.pairSheaf` and `.pairTransition`: the component sheaves
  and transitions of the system attached to a pair.
* `CategoryTheory.SimplicialSiteSituation.systemOfFibreTransitions`: a family of component
  sheaves with transitions satisfying the unit and cocycle laws, as a system in the sense of
  Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.pairSystem` and `.pairTotalSheaf`: that system for a
  pair, and the sheaf on the total site it descends to.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cartesianSheafEquivCartesianPair`: **Stacks 0D7I** for
  sheaves of sets. The category of cartesian sheaves of sets on the total site of a
  simplicial-site situation is equivalent to the category of pairs `(ℱ, α)`.
* `CategoryTheory.SimplicialSiteSituation.pairTotalSheaf_isCartesian`: the sheaf descended from a
  pair is cartesian.
* `CategoryTheory.SimplicialSiteSituation.pairTotalSheafPairIso`: its associated pair is the
  given pair, through the degree-zero identification `pairZeroIso`.

## Implementation notes

The equivalence is `cartesianPairFunctor.asEquivalence`, so its functor is the explicit one: the
degree-zero sheaf of the associated pair is the degree-zero restriction
(`cartesianPairFunctor_obj_sheaf`) and its comparison isomorphism is pinned by
`cartesianIso_hom_comp`. Nothing is chosen out of an existence statement.

The transition of the system at `φ : m ⟶ n` pulls back to the image of the last vertex of `⦋m⦌`
and then transports along the edge from there to the last vertex of `⦋n⦌`; this is possible
because a simplex map carries the last vertex weakly below the last vertex. Its unit law is the
right unit law of the compositor and its cocycle law is `edgeTransport_comp` together with
`edgeTransport_map`, so `systemOfFibreTransitions` applies.

Essential surjectivity needs the two face computations `pairTransition_face_zero` and
`pairTransition_face_one`: in degree one the edge of the system transition is degenerate for
`δ¹₀` and is the whole of `⦋1⦌` for `δ¹₁`, so the first transition is the inverse image of the
degree-zero identification and the second is that followed by `α`. This is exactly what makes
the comparison isomorphism of the descended sheaf equal to `α`.

A face `δ¹ₖ` has codomain `⦋0 + 1⦌` while a vertex or an edge of `⦋1⦌` has codomain `⦋1⦌`, so
the two readings of a degree-one object agree only up to an invisible numeral. The unit laws of
the compositor are therefore used through `pasteIsoOfEq_comp_id_eqToHom` and
`pasteIsoOfEq_id_comp_eqToHom`, which hold for an arbitrary simplex and absorb the transport
along the identification of the two readings, and the degree-one identities are assembled in
term mode.

Only the half of Stacks 0D7I concerning sheaves of **sets** is proved here; the tag therefore
carries the sub-key `"sheaves of sets"`. The case of sheaves of abelian groups is
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianAbPairEquivalence.lean`: it does not repeat
the descent construction, but transports the equivalence proved here through the identification
of abelian sheaves with internal commutative group objects in sheaves of sets, which is how the
abelian inverse image of Stacks 04JC is defined in the first place.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor
open scoped Simplicial

universe u

namespace SimplexCategory

/-- The image of the vertex of `⦋0⦌` under `δ¹₁` is the vertex `0` of `⦋1⦌`; the equality is
read in the codomain `⦋0 + 1⦌` of `δ¹₁`. -/
theorem vertexMap_zero_comp_delta_one :
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 ≫ δ (1 : Fin 2) =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0 := by
  apply Hom.ext_zero_left; rfl

/-- The image of the vertex of `⦋0⦌` under `δ¹₀` is the last vertex of `⦋1⦌`; the equality is
read in the codomain `⦋0 + 1⦌` of `δ¹₀`. -/
theorem vertexMap_zero_comp_delta_zero :
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 ≫ δ (0 : Fin 2) =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1 := by
  apply Hom.ext_zero_left; rfl

end SimplexCategory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### Systems from a family of transitions -/

/-- A family of sheaves on the components of a simplicial-site situation, with transitions
`f_φ⁻¹ Gₘ ⟶ Gₙ` satisfying the unit and cocycle laws of Stacks 09WF, as a system. -/
noncomputable def systemOfFibreTransitions
    (G : ∀ n : SimplexCategory, Sheaf (S.componentTopology n) (Type u))
    (t : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (S.transitionMorphism φ).inverseImage.obj (G m) ⟶ G n)
    (ht_id : ∀ n : SimplexCategory, t (𝟙 n) = (canonicalIdentityComparison S n).hom.app (G n))
    (ht_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (S.pasteIso ψ φ (G l)).hom ≫ t (ψ ≫ φ) =
        (S.transitionMorphism φ).inverseImage.map (t ψ) ≫ t φ) :
    SimplicialSheafSystem (componentPseudofunctor S) where
  app n := ((Functor.const _).obj (AsSmall.up.obj (G n.as))).toCatHom
  naturality f :=
    { toNatTrans :=
        { app := fun _ => AsSmall.up.map (t f.as)
          naturality := fun _ _ _ => by
            change AsSmall.up.map ((S.transitionMorphism f.as).inverseImage.map (𝟙 _)) ≫ _
              = _ ≫ 𝟙 _
            rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm } }
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    cat_disch
  naturality_id b := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext _
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalIdentityComparison S b.as).inv.app (G b.as)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map (t (𝟙 b.as)) =
      𝟙 (AsSmall.up.{u, u + 1, u + 1}.obj (G b.as))
    rw [← CategoryTheory.Functor.map_comp, ht_id, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    rfl
  naturality_comp := by
    intro b _ _ f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext _
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalCompositionComparison S f.as g.as).inv.app (G b.as)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map (t (f.as ≫ g.as)) =
      AsSmall.up.{u, u + 1, u + 1}.map
          ((S.transitionMorphism g.as).inverseImage.map (t f.as)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map (t g.as)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun x => AsSmall.up.{u, u + 1, u + 1}.map x) (ht_comp f.as g.as)

/-- The component in degree `n` of a system built from a family of transitions is the given
sheaf. -/
theorem systemSheaf_systemOfFibreTransitions
    (G : ∀ n : SimplexCategory, Sheaf (S.componentTopology n) (Type u))
    (t : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (S.transitionMorphism φ).inverseImage.obj (G m) ⟶ G n)
    (ht_id : ∀ n : SimplexCategory, t (𝟙 n) = (canonicalIdentityComparison S n).hom.app (G n))
    (ht_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (S.pasteIso ψ φ (G l)).hom ≫ t (ψ ≫ φ) =
        (S.transitionMorphism φ).inverseImage.map (t ψ) ≫ t φ) (n : SimplexCategory) :
    S.systemSheaf (S.systemOfFibreTransitions G t ht_id ht_comp) n = G n := rfl

/-- The transition of a system built from a family of transitions is the given transition. -/
theorem systemFibreTransition_systemOfFibreTransitions
    (G : ∀ n : SimplexCategory, Sheaf (S.componentTopology n) (Type u))
    (t : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (S.transitionMorphism φ).inverseImage.obj (G m) ⟶ G n)
    (ht_id : ∀ n : SimplexCategory, t (𝟙 n) = (canonicalIdentityComparison S n).hom.app (G n))
    (ht_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (S.pasteIso ψ φ (G l)).hom ≫ t (ψ ≫ φ) =
        (S.transitionMorphism φ).inverseImage.map (t ψ) ≫ t φ)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.systemFibreTransition (S.systemOfFibreTransitions G t ht_id ht_comp) φ = t φ := rfl

/-! ### The system attached to a pair -/

/-- The sheaf in degree `n` of the system attached to a pair: the inverse image of its
degree-zero sheaf along the last vertex of `⦋n⦌`. -/
noncomputable def pairSheaf (A : CartesianPair S) (n : SimplexCategory) :
    Sheaf (S.componentTopology n) (Type u) :=
  (S.transitionMorphism
    (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).inverseImage.obj A.sheaf

/-- The transition in the system attached to a pair, as an isomorphism: pull back to the image
of the last vertex and transport along the edge to the last vertex. -/
noncomputable def pairTransitionIso (A : CartesianPair S) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (S.pairSheaf A m) ≅ S.pairSheaf A n :=
  S.vertexPaste φ (Fin.last m.len) A.sheaf ≪≫
    S.edgeTransportIso A.sheaf A.iso (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _)

/-- The transition in the system attached to a pair. -/
noncomputable def pairTransition (A : CartesianPair S) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (S.pairSheaf A m) ⟶ S.pairSheaf A n :=
  (S.pairTransitionIso A φ).hom

/-- The transitions of the system attached to a pair are invertible. -/
instance pairTransition_isIso (A : CartesianPair S) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (S.pairTransition A φ) :=
  inferInstanceAs (IsIso (S.pairTransitionIso A φ).hom)

/-- The transitions of the system attached to a pair are compatible with composition. -/
theorem pairTransition_comp (A : CartesianPair S) {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    (S.pasteIso ψ φ (S.pairSheaf A l)).hom ≫ S.pairTransition A (ψ ≫ φ) =
      (S.transitionMorphism φ).inverseImage.map (S.pairTransition A ψ) ≫
        S.pairTransition A φ := by
  have hL : (S.pasteIso ψ φ (S.pairSheaf A l)).hom ≫ S.pairTransition A (ψ ≫ φ) =
      (S.pasteIso ψ φ ((S.transitionMorphism
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk l.len)
              (Fin.last l.len))).inverseImage.obj A.sheaf)).hom ≫
        (S.vertexPaste (ψ ≫ φ) (Fin.last l.len) A.sheaf).hom ≫
        S.edgeTransport A.sheaf A.iso (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len)))
          (Fin.last n.len) (Fin.le_last _) := rfl
  have hR : (S.transitionMorphism φ).inverseImage.map (S.pairTransition A ψ) ≫
        S.pairTransition A φ =
      (S.transitionMorphism φ).inverseImage.map
          ((S.vertexPaste ψ (Fin.last l.len) A.sheaf).hom ≫
            S.edgeTransport A.sheaf A.iso (ψ.toOrderHom (Fin.last l.len)) (Fin.last m.len)
              (Fin.le_last _)) ≫
        (S.vertexPaste φ (Fin.last m.len) A.sheaf).hom ≫
        S.edgeTransport A.sheaf A.iso (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
          (Fin.le_last _) := rfl
  rw [hL, hR, Functor.map_comp, Category.assoc,
    reassoc_of% (S.edgeTransport_map φ A.sheaf A.iso (ψ.toOrderHom (Fin.last l.len))
      (Fin.last m.len) (Fin.le_last _)),
    ← S.edgeTransport_comp A, ← Category.assoc, S.vertexPaste_comp ψ φ]
  exact (Category.assoc _ _ _).symm

/-- The transition at an identity simplex map is the canonical unit comparison. -/
theorem pairTransition_id (A : CartesianPair S) (n : SimplexCategory) :
    S.pairTransition A (𝟙 n) =
      (canonicalIdentityComparison S n).hom.app (S.pairSheaf A n) := by
  have h : S.pairTransition A (𝟙 n) =
      (S.pasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)) (𝟙 n)
          (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))
          (Category.comp_id _) A.sheaf).hom ≫
        S.edgeTransport A.sheaf A.iso (Fin.last n.len) (Fin.last n.len) le_rfl := rfl
  rw [h, S.edgeTransport_self A, Category.comp_id, S.pasteIsoOfEq_comp_id]
  rfl

/-- **Stacks 0D7I.** The simplicial system of sheaves attached to a pair. -/
noncomputable def pairSystem (A : CartesianPair S) :
    SimplicialSheafSystem (componentPseudofunctor S) :=
  S.systemOfFibreTransitions (S.pairSheaf A) (fun φ => S.pairTransition A φ)
    (S.pairTransition_id A) (fun ψ φ => S.pairTransition_comp A ψ φ)

/-- The component in degree `n` of the system attached to a pair. -/
theorem systemSheaf_pairSystem (A : CartesianPair S) (n : SimplexCategory) :
    S.systemSheaf (S.pairSystem A) n = S.pairSheaf A n := rfl

/-- The transition of the system attached to a pair. -/
theorem systemFibreTransition_pairSystem (A : CartesianPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) : S.systemFibreTransition (S.pairSystem A) φ = S.pairTransition A φ := rfl

/-! ### The sheaf descended from a pair -/

/-- **Stacks 0D7I.** The sheaf on the total site descended from a pair. -/
noncomputable def pairTotalSheaf (A : CartesianPair S) : Sheaf S.totalTopology (Type u) :=
  S.systemTotalSheaf (S.pairSystem A)

/-- The restriction of the sheaf descended from a pair to the component in degree `n` is the
component of the system. -/
noncomputable def pairRestrictIso (A : CartesianPair S) (n : SimplexCategory) :
    (S.restrict n).obj (S.pairTotalSheaf A) ≅ S.pairSheaf A n :=
  S.restrictIso (S.pairSystem A) n

/-- The canonical transition of the sheaf descended from a pair is the transition of the system,
conjugated by the fibrewise identifications. -/
theorem fiberTransition_pairTotalSheaf (A : CartesianPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.fiberTransition φ).app (S.pairTotalSheaf A) =
      (S.transitionMorphism φ).inverseImage.map (S.pairRestrictIso A m).hom ≫
        S.pairTransition A φ ≫ (S.pairRestrictIso A n).inv := by
  have h := S.restrictIso_systemFibreTransition (S.pairSystem A) φ
  change (S.fiberTransition φ).app (S.systemTotalSheaf (S.pairSystem A)) =
    (S.transitionMorphism φ).inverseImage.map (S.restrictIso (S.pairSystem A) m).hom ≫
      S.systemFibreTransition (S.pairSystem A) φ ≫ (S.restrictIso (S.pairSystem A) n).inv
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The canonical transition of the sheaf descended from a pair, followed by the identification
of the degree-`n` restriction, is the transition of the system. -/
theorem fiberTransition_pairTotalSheaf_comp_pairRestrictIso (A : CartesianPair S)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.fiberTransition φ).app (S.pairTotalSheaf A) ≫ (S.pairRestrictIso A n).hom =
      (S.transitionMorphism φ).inverseImage.map (S.pairRestrictIso A m).hom ≫
        S.pairTransition A φ := by
  rw [S.fiberTransition_pairTotalSheaf A φ, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Stacks 0D7I.** The sheaf descended from a pair is cartesian. -/
theorem pairTotalSheaf_isCartesian (A : CartesianPair S) :
    IsCartesianSheaf S (S.pairTotalSheaf A) := by
  intro m n φ
  rw [S.fiberTransition_pairTotalSheaf A φ]
  infer_instance

/-- The sheaf descended from a pair, as an object of the category of cartesian sheaves. -/
noncomputable def pairCartesianSheaf (A : CartesianPair S) : CartesianSheaf S :=
  ⟨S.pairTotalSheaf A, S.pairTotalSheaf_isCartesian A⟩

/-! ### The unit laws of the compositor, transported along an equality of simplex maps -/

/-- The right unit law of the compositor, followed by the transport along an equality
identifying the composite with the first factor. -/
theorem pasteIsoOfEq_comp_id_eqToHom {m n : SimplexCategory} (φ θ : m ⟶ n) (h : φ ≫ 𝟙 n = θ)
    (hθ : θ = φ) (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq φ (𝟙 n) θ h F).hom ≫
        eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) hθ) =
      (canonicalIdentityComparison S n).hom.app
        ((S.transitionMorphism φ).inverseImage.obj F) := by
  rw [S.pasteIsoOfEq_comp_id' φ θ h F, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- The left unit law of the compositor, followed by the transport along an equality identifying
the composite with the second factor. -/
theorem pasteIsoOfEq_id_comp_eqToHom {m n : SimplexCategory} (e : m ⟶ m) (he : e = 𝟙 m)
    (φ θ : m ⟶ n) (h : e ≫ φ = θ) (hθ : θ = φ)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq e φ θ h F).hom ≫
        eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) hθ) =
      (S.transitionMorphism φ).inverseImage.map
        (eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) he) ≫
          (canonicalIdentityComparison S m).hom.app F) := by
  rw [S.pasteIsoOfEq_id_comp' e he φ θ hθ.symm h F, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-! ### The pair of the descended sheaf -/

/-- The inverse image of the degree-zero sheaf of a pair along the only vertex of `⦋0⦌` is that
sheaf: the component in degree zero of the system attached to a pair is `ℱ`. -/
noncomputable def pairZeroIso (A : CartesianPair S) : S.pairSheaf A ⦋0⦌ ≅ A.sheaf :=
  eqToIso (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj A.sheaf)
      SimplexCategory.vertexMap_zero_zero) ≪≫
    (canonicalIdentityComparison S ⦋0⦌).app A.sheaf

/-- The inverse image of the degree-zero sheaf of a pair along the vertex `0` of `⦋1⦌` is its
inverse image along `δ¹₁`. -/
noncomputable def vertexFaceIsoOne (A : CartesianPair S) :
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 1) 0)).inverseImage.obj A.sheaf ≅
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj A.sheaf :=
  eqToIso (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj A.sheaf)
    SimplexCategory.vertexMap_one_zero)

/-- The inverse image of the degree-zero sheaf of a pair along the last vertex of `⦋1⦌`, which is
the component in degree one of the system, is its inverse image along `δ¹₀`. -/
noncomputable def vertexFaceIsoZero (A : CartesianPair S) :
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 1) 1)).inverseImage.obj A.sheaf ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj A.sheaf :=
  eqToIso (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj A.sheaf)
    SimplexCategory.vertexMap_one_one)

/-- The compositor at the factorization `δ¹₁ ≫ 𝟙` of the vertex `0` of `⦋1⦌`, followed by the
identification of that vertex with `δ¹₁`, is the canonical unit comparison. -/
theorem pasteIsoOfEq_comp_vertexFaceIsoOne (A : CartesianPair S) :
    (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2)) (𝟙 ⦋1⦌)
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)
          ((Category.comp_id _).trans SimplexCategory.vertexMap_one_zero.symm) A.sheaf).hom ≫
        (S.vertexFaceIsoOne A).hom =
      (canonicalIdentityComparison S ⦋1⦌).hom.app
        ((S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj A.sheaf) :=
  S.pasteIsoOfEq_comp_id_eqToHom _ _ _ SimplexCategory.vertexMap_one_zero A.sheaf

/-- The compositor at the factorization `δ¹₀ ≫ 𝟙` of the last vertex of `⦋1⦌`, followed by the
identification of that vertex with `δ¹₀`, is the canonical unit comparison. -/
theorem pasteIsoOfEq_comp_vertexFaceIsoZero (A : CartesianPair S) :
    (S.pasteIsoOfEq (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋1⦌)
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)
          ((Category.comp_id _).trans SimplexCategory.vertexMap_one_one.symm) A.sheaf).hom ≫
        (S.vertexFaceIsoZero A).hom =
      (canonicalIdentityComparison S ⦋1⦌).hom.app
        ((S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj A.sheaf) :=
  S.pasteIsoOfEq_comp_id_eqToHom _ _ _ SimplexCategory.vertexMap_one_one A.sheaf

/-- The compositor at the factorization of the vertex `0` of `⦋1⦌` through `δ¹₁`, followed by the
identification of that vertex with `δ¹₁`, is the inverse image of the degree-zero
identification. -/
theorem vertexPaste_comp_vertexFaceIsoOne (A : CartesianPair S) :
    (S.pasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0)
          (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)
          SimplexCategory.vertexMap_zero_comp_delta_one A.sheaf).hom ≫
        (S.vertexFaceIsoOne A).hom =
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
        (S.pairZeroIso A).hom :=
  S.pasteIsoOfEq_id_comp_eqToHom _ SimplexCategory.vertexMap_zero_zero _ _ _
    SimplexCategory.vertexMap_one_zero A.sheaf

/-- The compositor at the factorization of the last vertex of `⦋1⦌` through `δ¹₀`, followed by
the identification of that vertex with `δ¹₀`, is the inverse image of the degree-zero
identification. -/
theorem vertexPaste_comp_vertexFaceIsoZero (A : CartesianPair S) :
    (S.pasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0)
          (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)
          SimplexCategory.vertexMap_zero_comp_delta_zero A.sheaf).hom ≫
        (S.vertexFaceIsoZero A).hom =
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
        (S.pairZeroIso A).hom :=
  S.pasteIsoOfEq_id_comp_eqToHom _ SimplexCategory.vertexMap_zero_zero _ _ _
    SimplexCategory.vertexMap_one_one A.sheaf

/-- Transport along a simplex map equal to the identity of `⦋1⦌`, read between the inverse
images of `ℱ` along the two faces, is the comparison isomorphism of the pair. -/
theorem transportAlong_eq_pairIso (A : CartesianPair S) (e : ⦋1⦌ ⟶ ⦋1⦌) (he : e = 𝟙 ⦋1⦌)
    (v w : ⦋0⦌ ⟶ ⦋1⦌) (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ e = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ e = w) (hv : v = SimplexCategory.δ (1 : Fin 2))
    (hw : w = SimplexCategory.δ (0 : Fin 2)) :
    S.transportAlong A.sheaf A.iso e v w h₁ h₀ ≫
        eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj A.sheaf) hw) =
      eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj A.sheaf) hv) ≫
        A.iso.hom := by
  subst he
  subst hv
  subst hw
  have key : S.transportAlong A.sheaf A.iso (𝟙 ⦋1⦌) _ _ h₁ h₀ = A.iso.hom := by
    rw [S.transportAlong_eq, Iso.inv_comp_eq, S.pasteIsoOfEq_comp_id, S.pasteIsoOfEq_comp_id]
    exact (canonicalIdentityComparison S ⦋1⦌).hom.naturality A.iso.hom
  exact (Category.comp_id _).trans (key.trans (Category.id_comp _).symm)

/-- The edge transport across the whole of `⦋1⦌` is the comparison isomorphism of the pair. -/
theorem edgeTransport_one (A : CartesianPair S) :
    S.edgeTransport A.sheaf A.iso (0 : Fin 2) 1 (by decide) ≫ (S.vertexFaceIsoZero A).hom =
      (S.vertexFaceIsoOne A).hom ≫ A.iso.hom := by
  rw [S.edgeTransport_eq_transportAlong (n := 1) A.sheaf A.iso 0 1 (by decide) (𝟙 ⦋1⦌)
      (SimplexCategory.edgeMap_one_zero_one _)
      ((Category.comp_id _).trans SimplexCategory.vertexMap_one_zero.symm)
      ((Category.comp_id _).trans SimplexCategory.vertexMap_one_one.symm)]
  exact S.transportAlong_eq_pairIso A (𝟙 ⦋1⦌) rfl _ _ _ _
    SimplexCategory.vertexMap_one_zero SimplexCategory.vertexMap_one_one

/-- The transition of the system at `δ¹₀` is the inverse image of the degree-zero
identification. -/
theorem pairTransition_face_zero (A : CartesianPair S) :
    S.pairTransition A (SimplexCategory.δ (0 : Fin 2)) ≫ (S.vertexFaceIsoZero A).hom =
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
        (S.pairZeroIso A).hom := by
  have h : S.pairTransition A (SimplexCategory.δ (0 : Fin 2)) =
      (S.pasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0)
          (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)
          SimplexCategory.vertexMap_zero_comp_delta_zero A.sheaf).hom ≫
        S.edgeTransport A.sheaf A.iso (1 : Fin 2) 1 le_rfl := rfl
  rw [h, S.edgeTransport_self A, Category.comp_id]
  exact S.vertexPaste_comp_vertexFaceIsoZero A

/-- The transition of the system at `δ¹₁` is the inverse image of the degree-zero identification
followed by the comparison isomorphism of the pair. -/
theorem pairTransition_face_one (A : CartesianPair S) :
    S.pairTransition A (SimplexCategory.δ (1 : Fin 2)) ≫ (S.vertexFaceIsoZero A).hom =
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
          (S.pairZeroIso A).hom ≫ A.iso.hom := by
  have h : S.pairTransition A (SimplexCategory.δ (1 : Fin 2)) =
      (S.pasteIsoOfEq (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0)
          (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)
          SimplexCategory.vertexMap_zero_comp_delta_one A.sheaf).hom ≫
        S.edgeTransport A.sheaf A.iso (0 : Fin 2) 1 (by decide) := rfl
  rw [h]
  exact ((Category.assoc _ _ _).trans (_ ≫= S.edgeTransport_one A)).trans
    ((Category.assoc _ _ _).symm.trans (S.vertexPaste_comp_vertexFaceIsoOne A =≫ A.iso.hom))

/-- The identification of the degree-zero restriction of the sheaf descended from a pair with
the degree-zero sheaf of the pair. -/
noncomputable def pairTotalZeroIso (A : CartesianPair S) :
    (S.restrict ⦋0⦌).obj (S.pairTotalSheaf A) ≅ A.sheaf :=
  S.pairRestrictIso A ⦋0⦌ ≪≫ S.pairZeroIso A

/-- The identification of the degree-one restriction of the sheaf descended from a pair with the
inverse image of the degree-zero sheaf of the pair along `δ¹₀`. -/
noncomputable def pairTotalOneIso (A : CartesianPair S) :
    (S.restrict ⦋1⦌).obj (S.pairTotalSheaf A) ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj A.sheaf :=
  S.pairRestrictIso A ⦋1⦌ ≪≫ S.vertexFaceIsoZero A

/-- If the transition of the system along a face is `g` after the degree-one identification, so
is the canonical transition of the descended sheaf, after precomposing with the degree-zero
restriction. -/
private theorem fiberTransition_pairTotalSheaf_comp_pairTotalOneIso (A : CartesianPair S)
    (φ : ⦋0⦌ ⟶ ⦋1⦌)
    (g : (S.transitionMorphism φ).inverseImage.obj (S.pairSheaf A ⦋0⦌) ⟶
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj A.sheaf)
    (h : S.pairTransition A φ ≫ (S.vertexFaceIsoZero A).hom = g) :
    (S.fiberTransition φ).app (S.pairTotalSheaf A) ≫ (S.pairTotalOneIso A).hom =
      (S.transitionMorphism φ).inverseImage.map (S.pairRestrictIso A ⦋0⦌).hom ≫ g := by
  subst h
  exact ((Category.assoc _ _ _).symm.trans
    (S.fiberTransition_pairTotalSheaf_comp_pairRestrictIso A φ =≫ _)).trans (Category.assoc _ _ _)

/-- The canonical transition of the descended sheaf along `δ¹₀`, read through the degree-zero and
degree-one identifications, is the inverse image of the degree-zero identification. -/
theorem fiberTransition_pairTotalSheaf_face_zero (A : CartesianPair S) :
    (S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app (S.pairTotalSheaf A) ≫
        (S.pairTotalOneIso A).hom =
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
        (S.pairTotalZeroIso A).hom := by
  rw [S.fiberTransition_pairTotalSheaf_comp_pairTotalOneIso A _ _
    (S.pairTransition_face_zero A), ← Functor.map_comp]
  rfl

/-- The canonical transition of the descended sheaf along `δ¹₁`, read through the degree-zero and
degree-one identifications, is the inverse image of the degree-zero identification followed by
the comparison isomorphism of the pair. -/
theorem fiberTransition_pairTotalSheaf_face_one (A : CartesianPair S) :
    (S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).app (S.pairTotalSheaf A) ≫
        (S.pairTotalOneIso A).hom =
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
          (S.pairTotalZeroIso A).hom ≫ A.iso.hom := by
  rw [S.fiberTransition_pairTotalSheaf_comp_pairTotalOneIso A _ _
    (S.pairTransition_face_one A), ← Category.assoc, ← Functor.map_comp]
  rfl

/-- **Stacks 0D7I.** The pair attached to the sheaf descended from a pair is that pair. -/
noncomputable def pairTotalSheafPairIso (A : CartesianPair S) :
    S.cartesianPairFunctor.obj (S.pairCartesianSheaf A) ≅ A :=
  have hc : (S.cartesianIso (S.pairCartesianSheaf A)).hom ≫
        (S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app (S.pairTotalSheaf A) =
      (S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).app (S.pairTotalSheaf A) :=
    S.cartesianIso_hom_comp (S.pairCartesianSheaf A)
  have key : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
        (S.pairTotalZeroIso A).hom ≫ A.iso.hom =
      (S.cartesianIso (S.pairCartesianSheaf A)).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
          (S.pairTotalZeroIso A).hom :=
    ((((S.fiberTransition_pairTotalSheaf_face_one A).symm.trans (hc =≫ _).symm).trans
        (Category.assoc _ _ _)).trans
      (_ ≫= S.fiberTransition_pairTotalSheaf_face_zero A))
  CartesianPair.isoMk S (S.pairTotalZeroIso A) key

/-- **Stacks 0D7I.** Every pair is the pair of a cartesian sheaf of sets on the total site. -/
instance cartesianPairFunctor_essSurj : S.cartesianPairFunctor.EssSurj where
  mem_essImage A := ⟨S.pairCartesianSheaf A, ⟨S.pairTotalSheafPairIso A⟩⟩

/-- **Stacks 0D7I.** The functor from cartesian sheaves of sets to pairs is an equivalence. -/
instance cartesianPairFunctor_isEquivalence : S.cartesianPairFunctor.IsEquivalence := {}

/-- **Stacks 0D7I.** The category of cartesian sheaves of sets on the total site of a
simplicial-site situation is equivalent to the category of pairs `(ℱ, α)` consisting of a sheaf
of sets `ℱ` on the degree-zero component and an isomorphism `α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of
sheaves on the degree-one component satisfying the cocycle condition
`(f_{δ²₁})⁻¹α = (f_{δ²₀})⁻¹α ∘ (f_{δ²₂})⁻¹α` on the degree-two component. -/
@[stacks 0D7I "sheaves of sets"]
noncomputable def cartesianSheafEquivCartesianPair : CartesianSheaf S ≌ CartesianPair S :=
  S.cartesianPairFunctor.asEquivalence

end CategoryTheory.SimplicialSiteSituation

end
