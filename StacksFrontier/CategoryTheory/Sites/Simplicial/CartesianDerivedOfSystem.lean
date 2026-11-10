module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedPostnikov

/-!
# A cartesian simplicial system of the derived category comes from the total site

Let `S` be a simplicial-site situation and `T` a cartesian simplicial system of the derived
categories of its components, in the sense of Stacks 0D9G, whose objects have no positively
shifted self-maps. This file produces an object `K` of the derived category of abelian sheaves
on the total site which is cartesian in the sense of Stacks 07TF and whose associated simplicial
system, in the sense of Stacks 0D9H, is isomorphic to `T` compatibly with all the transitions.

The object is the totalization of the complex whose term in degree `n` is the extension by lower
shriek of the object of the system in degree `n`, that is, the derived colimit of the system
`n ↦ Yₙ⟦n⟧` of a sequential Postnikov system for that complex.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `realizationComponentComparison_isIso`: the restriction of the realization to degree `m` is the
  copower of the object of the system in degree `m`.
* `realization_component_iso`: the restriction of the totalization to degree `m` is the object of
  the system in degree `m`.
* `exists_isCartesianDerived_of_simplicialDerivedSystem`: Stacks 0D9L, a cartesian simplicial
  system whose objects have no positively shifted self-maps is the system associated with a
  cartesian object of the derived category of the total site.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D83](https://stacks.math.columbia.edu/tag/0D83)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived
  CategoryTheory.simplexCopower
  CategoryTheory.simplexCopowerAugmented
  CategoryTheory.SimplicialSiteSituation.realizationSimplicial
  CategoryTheory.SimplicialSiteSituation.realizationComplex
  CategoryTheory.SimplicialSiteSituation.realizationTerm

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- Countable direct sums of abelian sheaves exist and are exact. -/
theorem sheafHasExactCountableDirectSums {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) : HasExactCountableDirectSums (Sheaf J Ab.{u}) := by
  let _ : HasColimitsOfSize.{u, u} (Sheaf J Ab.{u}) := Sheaf.instHasColimitsOfSize
  let _ : AB5OfSize.{u, u} (Sheaf J Ab.{u}) := inferInstance
  let _ : HasFiniteBiproducts (Sheaf J Ab.{u}) := Abelian.hasFiniteBiproducts
  let _ : AB4OfSize.{u} (Sheaf J Ab.{u}) := AB4.of_AB5 _
  exact ⟨inferInstance, fun I _ => ⟨inferInstance, inferInstance⟩⟩

/-- The derived category of abelian sheaves has countable direct sums. -/
theorem derivedSheafHasCountableCoproducts {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasDerivedCategory.{v} (Sheaf J Ab.{u})] :
    HasCountableCoproducts (DerivedCategory (Sheaf J Ab.{u})) :=
  derivedCategory_hasCountableCoproducts _ (sheafHasExactCountableDirectSums J)

/-- Derived restriction to a simplicial degree preserves countable direct sums. -/
theorem derivedComponent_preservesCountableCoproducts (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete ℕ) (derivedComponent S n) := by
  let _ : PreservesColimits (S.abelianComponent n) :=
    Functor.preservesColimits_sheafPushforwardContinuous (S.inclusion n) Ab.{u}
      (S.componentTopology n) S.totalTopology
  let _ : PreservesColimitsOfShape (Discrete ℕ) (S.abelianComponent n) := by
    let _ : PreservesColimitsOfSize.{0, 0} (S.abelianComponent n) :=
      preservesColimitsOfSize_of_univLE.{u, u, 0, 0} _
    infer_instance
  exact mapDerivedCategory_preservesCountableCoproducts
    (sheafHasExactCountableDirectSums S.totalTopology)
    (sheafHasExactCountableDirectSums (S.componentTopology n)) (S.abelianComponent n)

/-- Derived restriction to a simplicial degree commutes with the shift by `ℤ`. -/
noncomputable local instance derivedComponent_commShift (n : SimplexCategory) :
    (derivedComponent S n).CommShift ℤ := by
  dsimp only [derivedComponent]
  infer_instance

/-- Derived restriction to a simplicial degree is a triangulated functor. -/
local instance derivedComponent_isTriangulated (n : SimplexCategory) :
    (derivedComponent S n).IsTriangulated := by
  dsimp only [derivedComponent]
  infer_instance

/-- The comparison of the restriction of the realization to degree `m` with the copower of the
object of the system in degree `m` is an isomorphism. -/
theorem realizationComponentComparison_isIso (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) (m : SimplexCategory) :
    IsIso (realizationComponentComparison S T hT m) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun n => ?_
  have (φ : n.unop ⟶ m) : IsIso (T.map φ) := hT φ
  let _ : Fintype (n.unop ⟶ m) := Fintype.ofFinite (n.unop ⟶ m)
  have he : (realizationComponentComparison S T hT m).app n =
      ((Limits.Sigma.mapIso fun φ : n.unop ⟶ m => (asIso (T.map φ)).symm) ≪≫
        (Limits.biproduct.isoCoproduct
          (fun φ : n.unop ⟶ m => (derivedInverseImage S φ).obj (T.obj n.unop))).symm ≪≫
        (realizationTermComponentIso S T m n.unop).symm).hom := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [realizationComponentComparison_ι, realizationComponentInclusion,
      realizationTermMap_homEquiv, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      Limits.Sigma.ι_mapIso_hom_assoc, Limits.biproduct.isoCoproduct_inv,
      Limits.Sigma.ι_comp_desc_assoc, realizationTermComponentIso_ι]
  rw [he]
  exact Iso.isIso_hom _

/-- **The realization has a totalization.** The realization complex carries a sequential
Postnikov system, and the system `n ↦ Yₙ⟦n⟧` of that Postnikov system has a derived colimit. -/
theorem exists_realization (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology k) Ab.{u}))
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ (P : Triangulated.SequentialPostnikovSystem (fun n : ℕ => realizationTerm S T ⦋n⦌)
        (fun n : ℕ => (realizationComplex T hT).d (n + 1) n))
      (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})),
      letI := derivedSheafHasCountableCoproducts S.totalTopology
      IsHomotopyColimit P.sequence K := by
  let _ := derivedSheafHasCountableCoproducts S.totalTopology
  obtain ⟨P⟩ := nonempty_sequentialPostnikovSystem_realizationComplex S T hT hHom
  exact ⟨P, Triangulated.exists_isHomotopyColimit P.sequence⟩

/-- **The restriction of the totalization to a simplicial degree is the object of the system**,
by an isomorphism which, composed after the restriction of `i`, is a left inverse of the inclusion
of each vertex. -/
theorem realization_component_iso (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology k) Ab.{u}))
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (P : Triangulated.SequentialPostnikovSystem (fun n : ℕ => realizationTerm S T ⦋n⦌)
      (fun n : ℕ => (realizationComplex T hT).d (n + 1) n))
    {K : DerivedCategory (Sheaf S.totalTopology Ab.{u})}
    (p : (letI := derivedSheafHasCountableCoproducts S.totalTopology
      ∐ P.sequence.obj) ⟶ K)
    (q : K ⟶ (shiftFunctor (DerivedCategory (Sheaf S.totalTopology Ab.{u})) (1 : ℤ)).obj
      (letI := derivedSheafHasCountableCoproducts S.totalTopology
        ∐ P.sequence.obj))
    (hK : letI := derivedSheafHasCountableCoproducts S.totalTopology
      Triangle.mk (Triangulated.telescopeMap P.sequence) p q ∈
        distTriang (DerivedCategory (Sheaf S.totalTopology Ab.{u})))
    (i : realizationTerm S T ⦋0⦌ ⟶ K)
    (hi : letI := derivedSheafHasCountableCoproducts S.totalTopology
      P.π 0 ≫ i =
        (shiftFunctorZero (DerivedCategory (Sheaf S.totalTopology Ab.{u})) ℤ).inv.app
          (P.obj 0) ≫ Limits.Sigma.ι P.sequence.obj 0 ≫ p)
    (m : SimplexCategory) :
    ∃ γ : (derivedComponent S m).obj K ≅ T.obj m,
      ∀ ψ : ⦋0⦌ ⟶ m, realizationComponentInclusion T hT ψ ≫
        (derivedComponent S m).map i ≫ γ.hom = 𝟙 _ := by
  let _ := derivedSheafHasCountableCoproducts S.totalTopology
  let _ := derivedSheafHasCountableCoproducts (S.componentTopology m)
  let _ := derivedComponent_preservesCountableCoproducts S m
  let _ := realizationComponentComparison_isIso S T hT m
  let e := asIso (realizationComponentComparison S T hT m)
  let B : SimplicialObject.Augmented
      (DerivedCategory (Sheaf (S.componentTopology m) Ab.{u})) :=
    { left := realizationSimplicial T hT ⋙ derivedComponent S m
      right := T.obj m
      hom := e.inv ≫ (simplexCopowerAugmented (T.obj m) m).hom }
  let eB : simplexCopowerAugmented (T.obj m) m ≅ B :=
    Comma.isoMk e (Iso.refl _) (by
      dsimp only [B, Functor.id_map, Iso.refl_hom]
      rw [Iso.hom_inv_id_assoc]
      simp)
  let ed := SimplicialObject.Augmented.ExtraDegeneracy.ofIso eB
    (simplexCopowerExtraDegeneracy (T.obj m) m)
  let ε := B.hom.app (Opposite.op ⦋0⦌)
  have hd (n : ℕ) : (derivedComponent S m).map ((realizationComplex T hT).d (n + 1) n) =
      AlgebraicTopology.AlternatingFaceMapComplex.objD B.left n := by
    simp only [realizationComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
      SimplicialObject.δ, B, Functor.comp_map]
  obtain ⟨hd₀, hc₀, hc⟩ := Triangulated.extraDegeneracy_contraction B ed
  have hvan (n : ℕ) (f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology m) Ab.{u}))
      ((n + 1 : ℕ) : ℤ)).obj ((derivedComponent S m).obj (realizationTerm S T ⦋n + 2⦌)) ⟶
      T.obj m) : f = 0 := by
    let a := (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology m) Ab.{u}))
        ((n + 1 : ℕ) : ℤ)).mapIso (e.app (Opposite.op ⦋n + 2⦌)).symm ≪≫
      Limits.PreservesCoproduct.iso (shiftFunctor
        (DerivedCategory (Sheaf (S.componentTopology m) Ab.{u})) ((n + 1 : ℕ) : ℤ))
        (fun _ : ⦋n + 2⦌ ⟶ m => T.obj m)
    exact hom_eq_zero_of_iso a (Iso.refl _) (fun g => hom_eq_zero_of_coproduct
      (fun _ : ⦋n + 2⦌ ⟶ m =>
        (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology m) Ab.{u}))
          ((n + 1 : ℕ) : ℤ)).obj (T.obj m))
      (fun _ => hHom m (n + 1) (by omega)) g) f
  obtain ⟨r, s, hr, hs, ht⟩ := (P.map (derivedComponent S m)).split_sequence (T.obj m) ε ed.s'
    ed.s ed.s'_comp_ε (by rwa [hd 0]) (by rwa [hd 0])
    (fun n => by rw [hd n, hd (n + 1)]; exact hc n) hvan
  obtain ⟨γ, hγ⟩ := Triangulated.exists_iso_of_split_restriction P (derivedComponent S m) p q hK
    i hi (T.obj m) ε r s hr hs ht
  refine ⟨γ, fun ψ => ?_⟩
  rw [hγ]
  change realizationComponentInclusion T hT ψ ≫ e.inv.app (Opposite.op ⦋0⦌) ≫
    Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ m => 𝟙 (T.obj m)) = 𝟙 _
  rw [← realizationComponentComparison_ι S T hT ψ]
  change (Limits.Sigma.ι (fun _ : ⦋0⦌ ⟶ m => T.obj m) ψ ≫ e.hom.app (Opposite.op ⦋0⦌)) ≫
    e.inv.app (Opposite.op ⦋0⦌) ≫ Limits.Sigma.desc _ = _
  simp

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- For a cartesian system `T`, a family of isomorphisms `γ : T ≅ V` compatible with the
transitions out of degree zero, through a morphism `β` in degree zero, is compatible with the
transitions along every simplex map. -/
theorem naturality_of_vertex_compatibility (T V : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) (β : T.obj ⦋0⦌ ⟶ V.obj ⦋0⦌)
    (γ : ∀ n, T.obj n ≅ V.obj n)
    (hγ : ∀ (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n),
      T.map ψ ≫ (γ n).hom = (derivedInverseImage S ψ).map β ≫ V.map ψ)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    T.map φ ≫ (γ n).hom =
      (derivedInverseImage S φ).map ((γ m).hom) ≫ V.map φ := by
  let ψ : ⦋0⦌ ⟶ m := SimplexCategory.const _ _ 0
  have := hT ψ
  refine (cancel_epi ((derivedInverseImage S φ).map (T.map ψ))).1 ?_
  refine (cancel_epi ((derivedInverseImageCompIso S ψ φ).hom.app (T.obj ⦋0⦌))).1 ?_
  have h := hγ n (ψ ≫ φ)
  rw [T.map_comp, V.map_comp] at h
  simp only [Category.assoc] at h ⊢
  rw [h, NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← (derivedInverseImage S φ).map_comp_assoc, ← hγ m ψ,
    (derivedInverseImage S φ).map_comp]
  simp only [Category.assoc]

/-- Transporting an isomorphism along equalities of its source and target. -/
theorem isIso_of_heq {C : Type*} [Category C] {X X' Y Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hX : X = X') (hY : Y = Y') (h : HEq f g) [IsIso f] : IsIso g := by
  subst hX hY
  cases h
  infer_instance

/-- An object of the derived category whose associated simplicial system is cartesian is a
cartesian object. -/
theorem isCartesianDerived_of_associatedDerivedSystem_cartesian
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (hK : SimplicialDerivedSystem.Cartesian (S.associatedDerivedSystem K)) :
    S.IsCartesianDerived K := by
  intro m n φ
  have : IsIso ((S.associatedDerivedSystemData K).val.map φ) := hK φ
  exact isIso_of_heq
    (congrArg (derivedInverseImage S φ).obj ((S.associatedDerivedSystemData K).property.1 m))
    ((S.associatedDerivedSystemData K).property.1 n)
    ((S.associatedDerivedSystemData K).property.2 φ)

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- A system isomorphic to a cartesian system is cartesian. -/
theorem cartesian_of_system_iso (T V : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) (γ : ∀ n, T.obj n ≅ V.obj n)
    (hγ : ∀ ⦃m n⦄ (φ : m ⟶ n), T.map φ ≫ (γ n).hom =
      (derivedInverseImage S φ).map ((γ m).hom) ≫ V.map φ) :
    SimplicialDerivedSystem.Cartesian V := by
  intro m n φ
  have := hT φ
  have h : V.map φ = (derivedInverseImage S φ).map ((γ m).inv) ≫ T.map φ ≫ (γ n).hom := by
    rw [hγ φ, ← Functor.map_comp_assoc]
    simp
  rw [h]
  infer_instance

/-- Naturality of a pair of morphisms that agree up to equalities of their sources and
targets. -/
theorem eqToHom_naturality_of_heq {C : Type*} [Category C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f ≫ eqToHom hY = eqToHom hX ≫ g := by
  subst hX hY
  cases h
  simp

/-- The objects of the associated simplicial system are the derived restrictions. -/
noncomputable def associatedComponentIso
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (n : SimplexCategory) :
    (S.associatedDerivedSystem K).obj n ≅ (derivedComponent S n).obj K :=
  eqToIso ((S.associatedDerivedSystemData K).property.1 n)

/-- The transitions of the associated simplicial system are the canonical derived
transitions. -/
theorem associatedComponentIso_naturality
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.associatedDerivedSystem K).map φ ≫ (associatedComponentIso S K n).hom =
      (derivedInverseImage S φ).map ((associatedComponentIso S K m).hom) ≫
        (derivedTransition S φ).app K := by
  refine Eq.trans ?_ (congrArg (fun k => k ≫ (derivedTransition S φ).app K)
    (eqToHom_map (derivedInverseImage S φ)
      ((S.associatedDerivedSystemData K).property.1 m))).symm
  exact eqToHom_naturality_of_heq
    (congrArg (derivedInverseImage S φ).obj
      ((S.associatedDerivedSystemData K).property.1 m))
    ((S.associatedDerivedSystemData K).property.1 n)
    ((S.associatedDerivedSystem K).map φ) ((derivedTransition S φ).app K)
    ((S.associatedDerivedSystemData K).property.2 φ)

/-- The comparison of the restrictions of the totalization with the objects of the system is
compatible with the transitions out of degree zero. -/
theorem realization_vertex_naturality (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    {K : DerivedCategory (Sheaf S.totalTopology Ab.{u})}
    (i : realizationTerm S T ⦋0⦌ ⟶ K)
    (γ : ∀ n, (derivedComponent S n).obj K ≅ T.obj n)
    (hγ : ∀ (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n),
      realizationComponentInclusion T hT ψ ≫
        (derivedComponent S n).map i ≫ (γ n).hom = 𝟙 _)
    (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
    T.map ψ ≫ (γ n).inv =
      (derivedInverseImage S ψ).map
          ((S.componentLowerShriekDerivedAdjunction ⦋0⦌).homEquiv _ _ i) ≫
        (derivedTransition S ψ).app K := by
  have := hT ψ
  have h : (γ n).inv = realizationComponentInclusion T hT ψ ≫ (derivedComponent S n).map i := by
    refine (cancel_mono (γ n).hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id] using (hγ n ψ).symm
  rw [h]
  simp only [realizationComponentInclusion, realizationTermMap_homEquiv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← derivedTransition_naturality]
  simp only [← Functor.map_comp_assoc]
  rfl

/-- A cartesian simplicial system of the derived categories of the components, whose objects have
no positively shifted self-maps, is the system associated with a cartesian object of the derived
category of the total site. -/
@[stacks 0D9L]
theorem exists_isCartesianDerived_of_simplicialDerivedSystem (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology k) Ab.{u}))
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ K : DerivedCategory (Sheaf S.totalTopology Ab.{u}),
      S.IsCartesianDerived K ∧
        ∃ γ : ∀ n, T.obj n ≅ (S.associatedDerivedSystem K).obj n,
          ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
            T.map φ ≫ (γ n).hom =
              (derivedInverseImage S φ).map ((γ m).hom) ≫
                (S.associatedDerivedSystem K).map φ := by
  let _ := derivedSheafHasCountableCoproducts S.totalTopology
  obtain ⟨P, K, p, q, hp⟩ := exists_realization S T hT hHom
  have := P.isIso_π_zero
  let i : realizationTerm S T ⦋0⦌ ⟶ K := inv (P.π 0) ≫
    (shiftFunctorZero (DerivedCategory (Sheaf S.totalTopology Ab.{u})) ℤ).inv.app (P.obj 0) ≫
      Limits.Sigma.ι P.sequence.obj 0 ≫ p
  have hi : P.π 0 ≫ i =
      (shiftFunctorZero (DerivedCategory (Sheaf S.totalTopology Ab.{u})) ℤ).inv.app (P.obj 0) ≫
        Limits.Sigma.ι P.sequence.obj 0 ≫ p := by
    simp [i]
  choose γ hγ using fun m => realization_component_iso S T hT hHom P p q hp i hi m
  let V := S.associatedDerivedSystem K
  let γ' (n : SimplexCategory) : T.obj n ≅ V.obj n :=
    (γ n).symm ≪≫ (associatedComponentIso S K n).symm
  let β := (S.componentLowerShriekDerivedAdjunction ⦋0⦌).homEquiv _ _ i ≫
    (associatedComponentIso S K ⦋0⦌).inv
  have hv (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
      T.map ψ ≫ (γ' n).hom = (derivedInverseImage S ψ).map β ≫ V.map ψ := by
    refine (cancel_mono (associatedComponentIso S K n).hom).1 ?_
    simp only [γ', Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [associatedComponentIso_naturality]
    simp only [β, Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    exact realization_vertex_naturality S T hT i γ hγ n ψ
  have hn ⦃m n : SimplexCategory⦄ (φ : m ⟶ n) :
      T.map φ ≫ (γ' n).hom =
        (derivedInverseImage S φ).map ((γ' m).hom) ≫ V.map φ :=
    naturality_of_vertex_compatibility S T V hT β γ' hv φ
  exact ⟨K, isCartesianDerived_of_associatedDerivedSystem_cartesian S K
    (cartesian_of_system_iso S T V hT γ' hn), γ', hn⟩

end CategoryTheory.SimplicialSiteSituation

end
