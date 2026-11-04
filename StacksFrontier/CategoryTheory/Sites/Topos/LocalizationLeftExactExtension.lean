module

public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Left exact functors out of a localized topos

Let `(C, J)` be a site and let `G` be a sheaf of sets on it. Write `C/G` for the site of elements
of `G` (Stacks 0791) and `j⁻¹ : Sh(C) ⥤ Sh(C/G)` for restriction along its projection, the inverse
image of the localization morphism `j_G`. Every sheaf `𝒦` on `C/G` is, canonically, an equalizer
```
  𝒦 ⟶ j⁻¹H ⇉ j⁻¹G
```
for a sheaf `H` on `C` with a map `φ : H ⟶ G`: by Stacks 0791, `𝒦` is the sheaf of fibres
`(U, s) ↦ {t ∈ H(U) | φ(t) = s}` of some such `φ`, the first parallel arrow is `j⁻¹φ`, and the
second one is the map to the terminal sheaf followed by the *tautological section*
`τ : * ⟶ j⁻¹G`, whose value at `(U, s)` is `s`.

Consequently a functor out of `Sh(C/G)` preserving finite limits is determined by its restriction
along `j⁻¹` together with its value at `τ`. This file proves the corresponding extension
statement: two such functors `A` and `B` together with an isomorphism `α : j⁻¹ ⋙ A ≅ j⁻¹ ⋙ B`
carrying `A(τ)` to `B(τ)` are isomorphic, by an isomorphism restricting to `α` along `j⁻¹`.

## Main definitions

* `CategoryTheory.Stacks.Topos.Localized.fiberInclusion`: the inclusion of the sheaf of fibres of
  `φ : H ⟶ G` into `j⁻¹H`.
* `CategoryTheory.Stacks.Topos.Localized.tautologicalSection`: the tautological section
  `τ : * ⟶ j⁻¹G`, as the fibre inclusion at `𝟙 G`.
* `CategoryTheory.Stacks.Topos.Localized.extendIso`: the isomorphism `A ≅ B` extending `α`.

## Main results

* `CategoryTheory.Stacks.Topos.Localized.isLimitFiberFork`: the sheaf of fibres of `φ` is the
  equalizer of `j⁻¹φ` and the tautological map.
* `CategoryTheory.Stacks.Topos.Localized.extendIso_hom_app_restriction`: `extendIso` restricts to
  `α` along `j⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite OverPresheafAux

universe w w' v u

namespace CategoryTheory.Stacks.Topos.Localized

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Sheaf J (Type v))

/-- The inclusion of the sheaf of fibres of `φ : H ⟶ G` into the restriction `j⁻¹H`: the fibre
`{t ∈ H(U) | φ(t) = s}` over `(U, s)` is a subset of `H(U)`. -/
def fiberInclusion :
    fiberFunctor G.obj J G.property ⟶ Over.forget G ⋙ restrictionFunctor G.obj J where
  app _ := ObjectProperty.homMk
    { app := fun _ ↦ ↾fun p ↦ p.val
      naturality := fun _ _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- The fibre inclusion is injective on sections. -/
theorem fiberInclusion_injective (T : Over G) (X : (CostructuredArrow yoneda G.obj)ᵒᵖ) :
    Function.Injective (((fiberInclusion J G).app T).hom.app X) :=
  fun _ _ h ↦ OverArrows.ext h

/-- The sheaf of fibres of the identity of `G`, which is a terminal sheaf on the site of elements:
its fibre over every `(U, s)` is the singleton `{s}`. -/
abbrev terminalFiber :
    Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) :=
  (fiberFunctor G.obj J G.property).obj (Over.mk (𝟙 G))

/-- The sheaf of fibres of the identity of `G` is terminal. -/
noncomputable def isTerminalTerminalFiber : IsTerminal (terminalFiber J G) :=
  (Over.mkIdTerminal (X := G)).isTerminalObj (fiberFunctor G.obj J G.property)

/-- The **tautological section** `τ : * ⟶ j⁻¹G` of the restriction of `G` to its site of elements:
its value at `(U, s)` is `s`. It is the fibre inclusion at the identity of `G`. -/
def tautologicalSection : terminalFiber J G ⟶ (restrictionFunctor G.obj J).obj G :=
  (fiberInclusion J G).app (Over.mk (𝟙 G))

/-- The tautological map `j⁻¹H ⟶ j⁻¹G`: the map to the terminal sheaf followed by `τ`. -/
noncomputable def tautologicalMap (H : Sheaf J (Type v)) :
    (restrictionFunctor G.obj J).obj H ⟶ (restrictionFunctor G.obj J).obj G :=
  (isTerminalTerminalFiber J G).from _ ≫ tautologicalSection J G

/-- The fibre inclusion equalizes `j⁻¹φ` and the tautological map. -/
theorem fiberInclusion_comp_restriction (T : Over G) :
    (fiberInclusion J G).app T ≫ (restrictionFunctor G.obj J).map T.hom =
      (fiberInclusion J G).app T ≫ tautologicalMap J G T.left := by
  have h := (fiberInclusion J G).naturality (Over.homMk T.hom : T ⟶ Over.mk (𝟙 G))
  have ht : (fiberInclusion J G).app T ≫
      (isTerminalTerminalFiber J G).from ((restrictionFunctor G.obj J).obj T.left) =
      (fiberFunctor G.obj J G.property).map (Over.homMk T.hom : T ⟶ Over.mk (𝟙 G)) :=
    (isTerminalTerminalFiber J G).hom_ext _ _
  simp only [Functor.comp_map, Over.forget_map, Over.homMk_left] at h
  rw [tautologicalMap, ← Category.assoc, ht]
  exact h.symm

/-- The fork exhibiting the sheaf of fibres of `φ` as an equalizer. -/
noncomputable abbrev fiberFork (T : Over G) :
    Fork ((restrictionFunctor G.obj J).map T.hom) (tautologicalMap J G T.left) :=
  Fork.ofι ((fiberInclusion J G).app T) (fiberInclusion_comp_restriction J G T)

/-- The value of the tautological map: it sends every section over `(U, s)` to `s`. -/
theorem tautologicalMap_app (H : Sheaf J (Type v)) (X : (CostructuredArrow yoneda G.obj)ᵒᵖ)
    (y : ((restrictionFunctor G.obj J).obj H).obj.obj X) :
    (tautologicalMap J G H).hom.app X y = yonedaEquiv X.unop.hom :=
  ((((isTerminalTerminalFiber J G).from ((restrictionFunctor G.obj J).obj H)).hom.app X) y).app_val

/-- **The sheaf of fibres of `φ : H ⟶ G` is the equalizer of `j⁻¹φ` and the tautological map.** -/
noncomputable def isLimitFiberFork (T : Over G) : IsLimit (fiberFork J G T) :=
  Fork.IsLimit.mk' _ fun s ↦ by
    refine ⟨ObjectProperty.homMk
      { app := fun X ↦ ↾fun y ↦ ⟨s.ι.hom.app X y, ⟨?_⟩⟩
        naturality := fun X Y g ↦ ?_ }, ?_, ?_⟩
    · have h := congrArg (fun m ↦ m.hom.app X y) s.condition
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        types_comp_apply] at h
      exact h.trans (tautologicalMap_app J G T.left X (s.ι.hom.app X y))
    · ext y
      exact OverArrows.ext (congrArg (fun f ↦ f y) (s.ι.hom.naturality g))
    · rfl
    · intro m hm
      ext X y
      exact OverArrows.ext (congrArg (fun f ↦ f.hom.app X y) hm)

section Extension

variable {𝒯 : Type w} [Category.{w'} 𝒯]
  (A B : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯)
  [PreservesFiniteLimits A] [PreservesFiniteLimits B]
  (α : restrictionFunctor G.obj J ⋙ A ≅ restrictionFunctor G.obj J ⋙ B)

/-- The image of the terminal sheaf of fibres under a left exact functor is terminal. -/
noncomputable def isTerminalMapTerminalFiber
    (A : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯)
    [PreservesFiniteLimits A] : IsTerminal (A.obj (terminalFiber J G)) :=
  (isTerminalTerminalFiber J G).isTerminalObj A

omit [PreservesFiniteLimits A] [PreservesFiniteLimits B] in
/-- Naturality of `α`, read on the restriction of a morphism of sheaves on `C`. -/
theorem map_restriction_comp {H H' : Sheaf J (Type v)} (f : H ⟶ H') :
    A.map ((restrictionFunctor G.obj J).map f) ≫ α.hom.app H' =
      α.hom.app H ≫ B.map ((restrictionFunctor G.obj J).map f) := by
  simpa only [Functor.comp_map] using α.hom.naturality f

variable (hτ : A.map (tautologicalSection J G) ≫ α.hom.app G =
  (isTerminalMapTerminalFiber J G B).from _ ≫ B.map (tautologicalSection J G))

include hτ in
omit [PreservesFiniteLimits A] in
/-- The compatibility of `α` with the tautological section, read on the tautological maps. -/
theorem map_tautologicalMap_comp (H : Sheaf J (Type v)) :
    A.map (tautologicalMap J G H) ≫ α.hom.app G = α.hom.app H ≫ B.map (tautologicalMap J G H) := by
  rw [tautologicalMap, A.map_comp, Category.assoc, hτ, ← Category.assoc, B.map_comp,
    ← Category.assoc]
  congr 1
  exact (isTerminalMapTerminalFiber J G B).hom_ext _ _

include hτ in
omit [PreservesFiniteLimits A] in
/-- The compatibility of `α` with the tautological section, in the inverse direction. -/
theorem map_tautologicalMap_comp_inv (H : Sheaf J (Type v)) :
    B.map (tautologicalMap J G H) ≫ α.inv.app G = α.inv.app H ≫ A.map (tautologicalMap J G H) := by
  rw [← cancel_epi (α.hom.app H), ← Category.assoc,
    ← map_tautologicalMap_comp J G A B α hτ H, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

/-- The underlying object over `G` of a sheaf `𝒦` on the site of elements: the sheaf `H` with
`φ : H ⟶ G` whose sheaf of fibres is `𝒦`. -/
noncomputable abbrev totalSheaf
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) : Over G :=
  (fiberFunctor G.obj J G.property).asEquivalence.inverse.obj K

/-- The inclusion of a sheaf `𝒦` on the site of elements into `j⁻¹H`, for `H` its total sheaf. -/
noncomputable def totalInclusion
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    K ⟶ (restrictionFunctor G.obj J).obj (totalSheaf J G K).left :=
  (fiberFunctor G.obj J G.property).asEquivalence.counitIso.inv.app K ≫
    (fiberInclusion J G).app (totalSheaf J G K)

/-- The total inclusion of `𝒦` equalizes `j⁻¹` of the structure map of its total sheaf and the
tautological map. -/
theorem totalInclusion_condition
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    totalInclusion J G K ≫ (restrictionFunctor G.obj J).map (totalSheaf J G K).hom =
      totalInclusion J G K ≫ tautologicalMap J G (totalSheaf J G K).left :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (fiberInclusion_comp_restriction J G (totalSheaf J G K))).trans (Category.assoc _ _ _).symm)

/-- **Every sheaf on the site of elements is an equalizer** `𝒦 ⟶ j⁻¹H ⇉ j⁻¹G` of `j⁻¹` of its
total sheaf's structure map and the tautological map. -/
noncomputable def isLimitTotalFork
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    IsLimit (Fork.ofι (totalInclusion J G K) (totalInclusion_condition J G K)) :=
  IsLimit.ofIsoLimit (isLimitFiberFork J G (totalSheaf J G K))
    (Fork.ext ((fiberFunctor G.obj J G.property).asEquivalence.counitIso.app K)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fiberInclusion J G).app
        (totalSheaf J G K))
          ((fiberFunctor G.obj J G.property).asEquivalence.counitIso.hom_inv_id_app K)).trans
            (Category.id_comp _))))

/-- The total inclusion is natural: for `g : 𝒦 ⟶ 𝒦'` it intertwines `g` with `j⁻¹` of the induced
map of total sheaves. -/
theorem totalInclusion_naturality
    {K K' : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)}
    (g : K ⟶ K') :
    g ≫ totalInclusion J G K' =
      totalInclusion J G K ≫ (restrictionFunctor G.obj J).map
        ((fiberFunctor G.obj J G.property).asEquivalence.inverse.map g).left := by
  have h1 := (fiberFunctor G.obj J G.property).asEquivalence.counitIso.inv.naturality g
  have h2 := (fiberInclusion J G).naturality
    ((fiberFunctor G.obj J G.property).asEquivalence.inverse.map g)
  simp only [Functor.id_map, Functor.comp_map, Over.forget_map] at h1 h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fiberInclusion J G).app
    (totalSheaf J G K')) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

/-- The equalizer fork of `𝒦`, after a left exact functor, is still a limit. -/
noncomputable def isLimitMapTotalFork
    (A : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯)
    [PreservesFiniteLimits A]
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    IsLimit (Fork.ofι (A.map (totalInclusion J G K))
      (by simp only [← A.map_comp, totalInclusion_condition]) :
      Fork (A.map ((restrictionFunctor G.obj J).map (totalSheaf J G K).hom))
        (A.map (tautologicalMap J G (totalSheaf J G K).left))) :=
  isLimitForkMapOfIsLimit A _ (isLimitTotalFork J G K)

/-- The image under `A` of the total inclusion of `𝒦`, followed by `α`, equalizes the images under
`B` of `j⁻¹` of the structure map of the total sheaf and of the tautological map. -/
theorem extendIso_condition
    {A B : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯}
    [PreservesFiniteLimits A] [PreservesFiniteLimits B]
    (α : restrictionFunctor G.obj J ⋙ A ≅ restrictionFunctor G.obj J ⋙ B)
    (hτ : A.map (tautologicalSection J G) ≫ α.hom.app G =
      (isTerminalMapTerminalFiber J G B).from _ ≫ B.map (tautologicalSection J G))
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    (A.map (totalInclusion J G K) ≫ α.hom.app (totalSheaf J G K).left) ≫
        B.map ((restrictionFunctor G.obj J).map (totalSheaf J G K).hom) =
      (A.map (totalInclusion J G K) ≫ α.hom.app (totalSheaf J G K).left) ≫
        B.map (tautologicalMap J G (totalSheaf J G K).left) := by
  rw [Category.assoc, ← map_restriction_comp J G A B α (totalSheaf J G K).hom, Category.assoc,
    ← map_tautologicalMap_comp J G A B α hτ, ← Category.assoc, ← Category.assoc, ← A.map_comp,
    ← A.map_comp, totalInclusion_condition]

/-- The component at `𝒦` of the extended isomorphism, in one direction: the lift through the
equalizer `B(𝒦)` of `A` of the total inclusion followed by `α`. -/
noncomputable def extendHomApp
    {A B : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯}
    [PreservesFiniteLimits A] [PreservesFiniteLimits B]
    (α : restrictionFunctor G.obj J ⋙ A ≅ restrictionFunctor G.obj J ⋙ B)
    (hτ : A.map (tautologicalSection J G) ≫ α.hom.app G =
      (isTerminalMapTerminalFiber J G B).from _ ≫ B.map (tautologicalSection J G))
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    A.obj K ⟶ B.obj K :=
  Fork.IsLimit.lift (isLimitMapTotalFork J G B K)
    (A.map (totalInclusion J G K) ≫ α.hom.app (totalSheaf J G K).left)
    (extendIso_condition J G α hτ K)

/-- `extendHomApp`, followed by the image under `B` of the total inclusion of `𝒦`, is the image
under `A` of the total inclusion followed by `α`. -/
theorem extendHomApp_comp
    {A B : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v) ⥤ 𝒯}
    [PreservesFiniteLimits A] [PreservesFiniteLimits B]
    (α : restrictionFunctor G.obj J ⋙ A ≅ restrictionFunctor G.obj J ⋙ B)
    (hτ : A.map (tautologicalSection J G) ≫ α.hom.app G =
      (isTerminalMapTerminalFiber J G B).from _ ≫ B.map (tautologicalSection J G))
    (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J) (Type v)) :
    extendHomApp J G α hτ K ≫ B.map (totalInclusion J G K) =
      A.map (totalInclusion J G K) ≫ α.hom.app (totalSheaf J G K).left :=
  Fork.IsLimit.lift_ι' (isLimitMapTotalFork J G B K) _ _

include hτ in
/-- The inverse of `α` also carries the tautological section of `B` to that of `A`. -/
theorem inv_tautologicalSection :
    B.map (tautologicalSection J G) ≫ α.inv.app G =
      (isTerminalMapTerminalFiber J G A).from _ ≫ A.map (tautologicalSection J G) := by
  rw [← cancel_mono (α.hom.app G), Category.assoc, Iso.inv_hom_id_app]
  refine (Category.comp_id _).trans ?_
  rw [Category.assoc, hτ, ← Category.assoc,
    show (isTerminalMapTerminalFiber J G A).from (B.obj (terminalFiber J G)) ≫
        (isTerminalMapTerminalFiber J G B).from (A.obj (terminalFiber J G)) = 𝟙 _ from
      (isTerminalMapTerminalFiber J G B).hom_ext _ _, Category.id_comp]

/-- **Extension of an isomorphism along restriction to the site of elements.** Two left exact
functors `A`, `B` out of `Sh(C/G)`, together with an isomorphism `α : j⁻¹ ⋙ A ≅ j⁻¹ ⋙ B` carrying
`A(τ)` to `B(τ)` for the tautological section `τ`, are isomorphic. -/
noncomputable def extendIso : A ≅ B :=
  NatIso.ofComponents
    (fun K ↦
      { hom := extendHomApp J G α hτ K
        inv := extendHomApp J G α.symm (inv_tautologicalSection J G A B α hτ) K
        hom_inv_id := by
          refine Fork.IsLimit.hom_ext (isLimitMapTotalFork J G A K) ?_
          change (_ ≫ _) ≫ A.map (totalInclusion J G K) = 𝟙 _ ≫ A.map (totalInclusion J G K)
          rw [Category.assoc, extendHomApp_comp, ← Category.assoc, extendHomApp_comp,
            Category.assoc, Iso.symm_hom, Iso.hom_inv_id_app]
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        inv_hom_id := by
          refine Fork.IsLimit.hom_ext (isLimitMapTotalFork J G B K) ?_
          change (_ ≫ _) ≫ B.map (totalInclusion J G K) = 𝟙 _ ≫ B.map (totalInclusion J G K)
          rw [Category.assoc, extendHomApp_comp, ← Category.assoc, extendHomApp_comp,
            Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app]
          exact (Category.comp_id _).trans (Category.id_comp _).symm })
    fun {K K'} g ↦ by
      refine Fork.IsLimit.hom_ext (isLimitMapTotalFork J G B K') ?_
      change (A.map g ≫ extendHomApp J G α hτ K') ≫ B.map (totalInclusion J G K') =
        (extendHomApp J G α hτ K ≫ B.map g) ≫ B.map (totalInclusion J G K')
      rw [Category.assoc, extendHomApp_comp, ← Category.assoc, ← A.map_comp,
        totalInclusion_naturality, A.map_comp, Category.assoc,
        map_restriction_comp J G A B α
          ((fiberFunctor G.obj J G.property).asEquivalence.inverse.map g).left,
        ← Category.assoc, ← extendHomApp_comp, Category.assoc, ← B.map_comp,
        ← totalInclusion_naturality, B.map_comp, Category.assoc]

/-- The components of the extended isomorphism are the maps `extendHomApp`. -/
theorem extendIso_hom_app (K : Sheaf ((CostructuredArrow.proj yoneda G.obj).restrictedTopology J)
    (Type v)) :
    (extendIso J G A B α hτ).hom.app K = extendHomApp J G α hτ K :=
  rfl

/-- The homomorphism of `homEquivFiberSheaf` is postcomposition of the fibre inclusion with the
restriction of the morphism. -/
theorem homEquivFiberSheaf_apply (T : Over G) (H : Sheaf J (Type v)) (b : T.left ⟶ H) :
    homEquivFiberSheaf G.obj J G.property T H b =
      (fiberInclusion J G).app T ≫ (restrictionFunctor G.obj J).map b :=
  rfl

/-- **`extendIso` restricts to `α`.** On a restriction `j⁻¹H` the extended isomorphism is the given
one. -/
theorem extendIso_hom_app_restriction (H : Sheaf J (Type v)) :
    (extendIso J G A B α hτ).hom.app ((restrictionFunctor G.obj J).obj H) = α.hom.app H := by
  let K := (restrictionFunctor G.obj J).obj H
  let e := (fiberFunctor G.obj J G.property).asEquivalence
  let r : (totalSheaf J G K).left ⟶ H := (homEquivFiberSheaf G.obj J G.property _ H).symm
    (e.counitIso.hom.app K)
  have h : (fiberInclusion J G).app (totalSheaf J G K) ≫ (restrictionFunctor G.obj J).map r =
      e.counitIso.hom.app K :=
    (homEquivFiberSheaf_apply J G _ H r).symm.trans (Equiv.apply_symm_apply _ _)
  have hr : totalInclusion J G K ≫ (restrictionFunctor G.obj J).map r = 𝟙 K :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans (e.counitIso.inv_hom_id_app K))
  rw [extendIso_hom_app, ← Category.comp_id (extendHomApp J G α hτ K), ← B.map_id K, ← hr,
    B.map_comp, ← Category.assoc, extendHomApp_comp, Category.assoc,
    ← map_restriction_comp J G A B α r, ← Category.assoc, ← A.map_comp, hr, A.map_id,
    Category.id_comp]

end Extension

end CategoryTheory.Stacks.Topos.Localized

end
