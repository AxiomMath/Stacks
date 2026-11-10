module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFullness
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.HomPresheaf

/-!
# Descent, Lemma 0GN7 over a base which is not affine

Tag 03DU attaches to a quasi-coherent module `M` on a scheme `S` a presheaf of modules `Mᵃ` on a
site `C` of schemes over `S`, and Descent, Lemma 0GN7 asserts that `M ↦ Mᵃ` is fully faithful on
quasi-coherent modules. This file proves both halves over a base `S` which is not assumed affine,
on a site for which the presheaf of morphisms of pullbacks is a sheaf and the objects with affine
underlying scheme cover every object.

## Main results

* `Stacks.Sites.localHom`: the component of a map `a : Mᵃ ⟶ Nᵃ` at an object with affine
  underlying scheme, read as a morphism of the pullbacks of `M` and `N`.
* `Stacks.Sites.presheafHom_toOver_map_localHom`: those morphisms are compatible with the
  restriction maps of the presheaf of morphisms.
* `Stacks.Sites.localHomFamily` and `Stacks.Sites.localHomFamily_compatible`: they form a
  compatible family for the presieve of arrows with affine source.
* `Stacks.Sites.exists_hom_associatedModuleMap_app_eq_of_isPrestack`: **the affine-local half of
  the fullness clause of Descent, Lemma 0GN7 over an arbitrary base** — the hypothesis `haff` of
  `Stacks.Sites.surjective_associatedModuleMap_of_isAffine`, with no affineness assumption on `S`.
* `Stacks.Sites.surjective_associatedModuleMap_of_isPrestack` and
  `Stacks.Sites.associatedModuleMap_injective_of_isPrestack`: the fullness and the faithfulness
  clause over an arbitrary base.
* `Stacks.Sites.bijective_associatedModuleMap_of_isPrestack`: **the conclusion of Descent, Lemma
  0GN7 over an arbitrary base.**
* `Stacks.Sites.full_associatedModuleFunctor_of_isPrestack` and
  `Stacks.Sites.faithful_associatedModuleFunctor_of_isPrestack`: the same as fullness and
  faithfulness of `Stacks.Sites.associatedModuleFunctor`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-! ### The presheaf of morphisms of pullbacks on a site of schemes -/

section Comparison

variable {M N : S.Modules}

/-- The comparison isomorphism of iterated pullback along an arrow of the site: pulling back to
the target of the arrow and then along the arrow is pulling back to its source. -/
public noncomputable def pullComparison {X Y : C} (q : Y ⟶ X) :
    Scheme.Modules.pullback (toOver.obj X).hom ⋙
        Scheme.Modules.pullback (toOver.map q).left ≅
      Scheme.Modules.pullback (toOver.obj Y).hom :=
  Scheme.Modules.pullbackComp (toOver.map q).left (toOver.obj X).hom ≪≫
    Scheme.Modules.pullbackCongr (Over.w (toOver.map q))

/-- **The restriction map of the presheaf of morphisms of pullbacks on a site of schemes.**  It is
the pullback map on morphisms, conjugated by `Stacks.Sites.pullComparison`. -/
public theorem presheafHom_toOver_map {X Y : C} (q : Y ⟶ X)
    (φ : (Scheme.Modules.pullback (toOver.obj X).hom).obj M ⟶
      (Scheme.Modules.pullback (toOver.obj X).hom).obj N) :
    (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map q.op φ =
      (pullComparison S toOver q).inv.app M ≫
        (Scheme.Modules.pullback (toOver.map q).left).map φ ≫
          (pullComparison S toOver q).hom.app N := by
  refine (modulePullbackPseudofunctor_pullHom (toOver.map q).left (toOver.obj X).hom
    (toOver.obj Y).hom (Over.w (toOver.map q)) M N φ).trans ?_
  simp only [pullComparison, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rfl

/-- `Stacks.Sites.presheafHom_toOver_map` in the form that compares a restriction with a given
morphism of pullbacks at the source. -/
public theorem presheafHom_toOver_map_eq_iff {X Y : C} (q : Y ⟶ X)
    (φ : (Scheme.Modules.pullback (toOver.obj X).hom).obj M ⟶
      (Scheme.Modules.pullback (toOver.obj X).hom).obj N)
    (ψ : (Scheme.Modules.pullback (toOver.obj Y).hom).obj M ⟶
      (Scheme.Modules.pullback (toOver.obj Y).hom).obj N) :
    (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map q.op φ = ψ ↔
      (Scheme.Modules.pullback (toOver.map q).left).map φ ≫
          (pullComparison S toOver q).hom.app N =
        (pullComparison S toOver q).hom.app M ≫ ψ := by
  rw [presheafHom_toOver_map]
  constructor
  · intro h
    rw [← h, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro h
    rw [h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **The unit of the pullback–pushforward adjunction followed by the comparison isomorphism acts
on global sections as the pullback map on sections of Tag 03DS.** -/
public theorem unit_comp_pullComparison_app_top (P : S.Modules) {X Y : C} (q : Y ⟶ X)
    (m : Γ((Scheme.Modules.pullback (toOver.obj X).hom).obj P, ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (toOver.map q).left).unit.app
          ((Scheme.Modules.pullback (toOver.obj X).hom).obj P) ≫
        (Scheme.Modules.pushforward (toOver.map q).left).map
          ((pullComparison S toOver q).hom.app P)).app ⊤ m =
      pullbackSectionsMap P (toOver.map q) m := by
  have h := unit_comp_pushforward_map_app_top P (toOver.map q)
    (𝟙 ((Scheme.Modules.pullback (toOver.obj Y).hom).obj P)) m
  rw [Category.comp_id] at h
  simp only [Functor.map_comp, Scheme.Modules.Hom.id_app] at h
  exact h

/-- **The restriction maps of the presheaf of morphisms fix the pullbacks of a morphism on the
base.** -/
public theorem presheafHom_toOver_map_pullbackMap {X Y : C} (q : Y ⟶ X) (φ : M ⟶ N) :
    (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map q.op
        ((Scheme.Modules.pullback (toOver.obj X).hom).map φ) =
      (Scheme.Modules.pullback (toOver.obj Y).hom).map φ := by
  rw [presheafHom_toOver_map_eq_iff]
  exact (pullComparison S toOver q).hom.naturality φ

end Comparison

/-! ### Reading a component of a map of associated modules at an affine object -/

section Local

variable {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- **The component of a map of associated presheaves of modules at an object with affine
underlying scheme, read as a morphism of the pullbacks.**  On an affine scheme a `Γ(T, 𝒪)`-linear
map between the global sections of two quasi-coherent modules is the action on global sections of
a morphism of modules, which is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`; this is the morphism it returns at
the component of `a`. -/
public noncomputable def localHom
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver)
    (X : C) (hX : IsAffine (toOver.obj X).left) :
    (Scheme.Modules.pullback (toOver.obj X).hom).obj M ⟶
      (Scheme.Modules.pullback (toOver.obj X).hom).obj N :=
  have := hX
  (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq
    (F := (Scheme.Modules.pullback (toOver.obj X).hom).obj M)
    (G := (Scheme.Modules.pullback (toOver.obj X).hom).obj N) (a.app (op X)).hom).choose

/-- `Stacks.Sites.localHom` acts on global sections as the component of `a`. -/
public theorem localHom_app_top
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver)
    (X : C) (hX : IsAffine (toOver.obj X).left)
    (m : Γ((Scheme.Modules.pullback (toOver.obj X).hom).obj M, ⊤)) :
    (localHom S toOver a X hX).app ⊤ m = (a.app (op X)).hom m :=
  have := hX
  (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq
    (F := (Scheme.Modules.pullback (toOver.obj X).hom).obj M)
    (G := (Scheme.Modules.pullback (toOver.obj X).hom).obj N)
    (a.app (op X)).hom).choose_spec m

/-- **`Stacks.Sites.localHom` is compatible with the restriction maps of the presheaf of
morphisms, between two objects with affine underlying scheme.** -/
public theorem presheafHom_toOver_map_localHom
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver)
    {X Y : C} (f : Y ⟶ X) (hX : IsAffine (toOver.obj X).left)
    (hY : IsAffine (toOver.obj Y).left) :
    (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map f.op
        (localHom S toOver a X hX) = localHom S toOver a Y hY := by
  have := hX
  have := hY
  rw [presheafHom_toOver_map_eq_iff]
  refine Scheme.Modules.hom_ext_of_unit_app_top (toOver.map f).left
    ((Scheme.Modules.pullback (toOver.obj X).hom).obj M)
    ((Scheme.Modules.pullback (toOver.obj Y).hom).obj N) (fun m => ?_)
  have hnatu : (Scheme.Modules.pullbackPushforwardAdjunction (toOver.map f).left).unit.app
        ((Scheme.Modules.pullback (toOver.obj X).hom).obj M) ≫
      (Scheme.Modules.pushforward (toOver.map f).left).map
        ((Scheme.Modules.pullback (toOver.map f).left).map (localHom S toOver a X hX)) =
      localHom S toOver a X hX ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (toOver.map f).left).unit.app
          ((Scheme.Modules.pullback (toOver.obj X).hom).obj N) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (toOver.map f).left).unit.naturality
      (localHom S toOver a X hX)).symm
  have hL : (((Scheme.Modules.pullbackPushforwardAdjunction (toOver.map f).left).unit.app
          ((Scheme.Modules.pullback (toOver.obj X).hom).obj M) ≫
        (Scheme.Modules.pushforward (toOver.map f).left).map
          ((Scheme.Modules.pullback (toOver.map f).left).map (localHom S toOver a X hX) ≫
            (pullComparison S toOver f).hom.app N)).app ⊤) m =
      pullbackSectionsMap N (toOver.map f) ((localHom S toOver a X hX).app ⊤ m) := by
    rw [Functor.map_comp, ← Category.assoc, hnatu, Category.assoc]
    exact unit_comp_pullComparison_app_top S toOver N f ((localHom S toOver a X hX).app ⊤ m)
  refine hL.trans (Eq.trans ?_ (unit_comp_pushforward_map_app_top M (toOver.map f)
    (localHom S toOver a Y hY) m).symm)
  rw [localHom_app_top S toOver a X hX m,
    localHom_app_top S toOver a Y hY (pullbackSectionsMap M (toOver.map f) m)]
  exact (PresheafOfModules.naturality_apply a f.op m).symm

/-! ### The presieve of the affine objects -/

/-- The presieve on an object of the site consisting of **all** arrows whose source has affine
underlying scheme. -/
public def affinePresieve (X : C) : Presieve X :=
  fun ⦃Z⦄ _ => IsAffine (toOver.obj Z).left

/-- **`Stacks.Sites.affinePresieve` generates the sieve of arrows factoring through an affine
object.** -/
public theorem generate_affinePresieve (X : C) :
    Sieve.generate (affinePresieve S toOver X) =
      Sieve.coverByImage (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X := by
  ext Z f
  constructor
  · rintro ⟨W, l, q, hq, rfl⟩
    exact ⟨⟨⟨W, hq⟩, l, q, rfl⟩⟩
  · rintro ⟨⟨W, l, q, rfl⟩⟩
    exact ⟨W.obj, l, q, W.property, rfl⟩

/-- The family of elements of the presheaf of morphisms indexed by
`Stacks.Sites.affinePresieve`, sending an arrow with affine source to `Stacks.Sites.localHom` of
its source. -/
public noncomputable def localHomFamily
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver) (X : C) :
    Presieve.FamilyOfElements
      (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N) (affinePresieve S toOver X) :=
  fun _ _ hf => localHom S toOver a _ hf

omit [M.IsQuasicoherent] [N.IsQuasicoherent] in
/-- Two successive restriction maps of the presheaf of morphisms compose. -/
public theorem presheafHom_map_map {X Y Z : C} (g : Z ⟶ Y) (v : X ⟶ Z)
    (x : (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).obj (op Y)) :
    (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map v.op
        ((toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map g.op x) =
      (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map (v ≫ g).op x := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- The presheaf of morphisms is a sheaf for `Stacks.Sites.affinePresieve` as soon as it is a
sheaf for the covering sieves of the affine objects. -/
private theorem isSheafFor_affinePresieve {M N : S.Modules} (J : GrothendieckTopology C)
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X) (X : C) :
    Presieve.IsSheafFor (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N)
      (affinePresieve S toOver X) := by
  rw [Presieve.isSheafFor_iff_generate, generate_affinePresieve]
  exact hH _ (hcover X)

omit [M.IsQuasicoherent] [N.IsQuasicoherent] in
/-- **The presheaf of morphisms is separated for `Stacks.Sites.affinePresieve`** as soon as it is
a sheaf for the covering sieves of the affine objects. -/
public theorem isSeparatedFor_affinePresieve (J : GrothendieckTopology C)
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X) (X : C) :
    Presieve.IsSeparatedFor (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N)
      (affinePresieve S toOver X) :=
  (isSheafFor_affinePresieve S toOver J hH hcover X).isSeparatedFor

/-- **`Stacks.Sites.localHomFamily` is compatible**, as soon as the arrows factoring through an
affine object cover every object and the presheaf of morphisms is a sheaf. -/
public theorem localHomFamily_compatible (J : GrothendieckTopology C)
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver) (X₀ : C) :
    (localHomFamily S toOver a X₀).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
  refine (isSeparatedFor_affinePresieve S toOver J hH hcover Z).ext (fun V v hv => ?_)
  have key : ∀ (Y : C) (g : Z ⟶ Y) (hY : IsAffine (toOver.obj Y).left),
      (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map v.op
          ((toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map g.op
            (localHom S toOver a Y hY)) = localHom S toOver a V hv := by
    intro Y g hY
    exact (presheafHom_map_map S toOver g v (localHom S toOver a Y hY)).trans
      (presheafHom_toOver_map_localHom S toOver a (v ≫ g) hY hv)
  exact (key Y₁ g₁ h₁).trans (key Y₂ g₂ h₂).symm

/-! ### Descent, Lemma 0GN7 over an arbitrary base -/

variable (J : GrothendieckTopology C)

/-- **The affine-local half of the fullness clause of Descent, Lemma 0GN7 over an arbitrary
base.**  Let `toOver : C ⥤ Over S` present a category of schemes over a base `S` which is *not*
assumed affine, carried by a topology `J` for which the presheaf of morphisms of pullbacks of `M`
and `N` is a sheaf and the arrows factoring through an object with affine underlying scheme cover
every object, and which contains an object `X₀` with invertible structure morphism receiving a
morphism from every object.  Then every map `a : Mᵃ ⟶ Nᵃ` of associated presheaves of modules
agrees, over the objects with affine underlying scheme, with the map induced by some morphism
`φ : M ⟶ N`. -/
public theorem exists_hom_associatedModuleMap_app_eq_of_isPrestack
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀))
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver) :
    ∃ φ : M ⟶ N, ∀ X : C, IsAffine (toOver.obj X).left →
      (associatedModuleMap S toOver φ).app (op X) = a.app (op X) := by
  obtain ⟨t, ht, -⟩ := isSheafFor_affinePresieve S toOver J hH hcover X₀
    (localHomFamily S toOver a X₀)
    (localHomFamily_compatible S toOver J hH hcover a X₀)
  obtain ⟨φ, hφ⟩ := Functor.Full.map_surjective
    (F := Scheme.Modules.pullback (toOver.obj X₀).hom) t
  refine ⟨φ, fun X hX => ?_⟩
  obtain ⟨f⟩ := hterm X
  have h1 : (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N).map f.op t
      = localHom S toOver a X hX := ht f hX
  rw [← hφ, presheafHom_toOver_map_pullbackMap] at h1
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((Scheme.Modules.pullback (toOver.obj X).hom).map φ).app ⊤ m = _
  rw [h1]
  exact localHom_app_top S toOver a X hX m

/-- **The faithfulness clause of Descent, Lemma 0GN7 over an arbitrary base.**  A morphism of
quasi-coherent modules on a base which is not assumed affine is determined by the induced maps on
the sections of the associated presheaves of modules, on a site satisfying the same hypotheses. -/
public theorem associatedModuleMap_injective_of_isPrestack
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] :
    Function.Injective fun φ : M ⟶ N => associatedModuleMap S toOver φ := by
  intro φ ψ h
  have h' : associatedModuleMap S toOver φ = associatedModuleMap S toOver ψ := h
  refine Functor.map_injective (Scheme.Modules.pullback (toOver.obj X₀).hom) ?_
  refine (isSeparatedFor_affinePresieve S toOver J hH hcover X₀).ext (fun V v hv => ?_)
  have : IsAffine (toOver.obj V).left := hv
  refine ((presheafHom_toOver_map_pullbackMap S toOver v φ).trans ?_).trans
    (presheafHom_toOver_map_pullbackMap S toOver v ψ).symm
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top (fun m => ?_)
  exact congrArg (fun b : associatedModulePresheaf S M toOver ⟶
    associatedModulePresheaf S N toOver => (b.app (op V)).hom m) h'

/-- **The fullness clause of Descent, Lemma 0GN7 over an arbitrary base.**  Under the hypotheses
of `Stacks.Sites.exists_hom_associatedModuleMap_app_eq_of_isPrestack` the map `φ ↦ φᵃ` is
surjective on morphisms of quasi-coherent modules. -/
public theorem surjective_associatedModuleMap_of_isPrestack
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  surjective_associatedModuleMap_of_isAffine S toOver J hN hcover
    (exists_hom_associatedModuleMap_app_eq_of_isPrestack S toOver J hH hcover X₀ hterm)

/-- **Descent, Lemma 0GN7 over an arbitrary base.**  On a site of schemes over a base `S` which is
not assumed affine, satisfying the hypotheses of
`Stacks.Sites.exists_hom_associatedModuleMap_app_eq_of_isPrestack`, the map `φ ↦ φᵃ` is bijective
on morphisms of quasi-coherent modules, which is full faithfulness of `M ↦ Mᵃ` at the pair
`(M, N)`. -/
public theorem bijective_associatedModuleMap_of_isPrestack
    (hH : Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N))
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    Function.Bijective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  ⟨associatedModuleMap_injective_of_isPrestack S toOver J hH hcover X₀,
    surjective_associatedModuleMap_of_isPrestack S toOver J hH hN hcover X₀ hterm⟩

end Local

/-! ### Full faithfulness of the functor over an arbitrary base -/

section Functor

variable (J : GrothendieckTopology C)

/-- **The functor `M ↦ Mᵃ` is full as soon as `φ ↦ φᵃ` is surjective at every pair of
quasi-coherent modules on `S`.** -/
public theorem full_associatedModuleFunctor_of_surjective
    (hsurj : ∀ (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent],
      Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ) :
    (associatedModuleFunctor S toOver).Full := by
  constructor
  intro F G f
  have := F.property
  have := G.property
  obtain ⟨φ, hφ⟩ := hsurj _ _ f
  exact ⟨ObjectProperty.homMk φ, hφ⟩

/-- **The functor `M ↦ Mᵃ` is faithful as soon as `φ ↦ φᵃ` is injective at every pair of
quasi-coherent modules on `S`.** -/
public theorem faithful_associatedModuleFunctor_of_injective
    (hinj : ∀ (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent],
      Function.Injective fun φ : M ⟶ N => associatedModuleMap S toOver φ) :
    (associatedModuleFunctor S toOver).Faithful := by
  constructor
  intro F G φ ψ h
  have := F.property
  have := G.property
  exact ObjectProperty.hom_ext _ (hinj _ _ h)

/-- **The descent property for morphisms of the pullbacks of quasi-coherent modules on `S`, along
the coverings of the site**: for all quasi-coherent modules `M` and `N` on `S`, the presheaf of
morphisms of the pullbacks of `M` and `N` is a sheaf for `J`. -/
public def IsPrestackOver : Prop :=
  ∀ (M N : S.Modules), M.IsQuasicoherent → N.IsQuasicoherent →
    Presieve.IsSheaf J (toOver.op ⋙ modulePullbackPseudofunctor.presheafHom M N)

/-- **Descent, Lemma 0GN7 over an arbitrary base, faithfulness clause, as a property of the
functor.**  On a site satisfying the hypotheses of
`Stacks.Sites.associatedModuleMap_injective_of_isPrestack` for every pair of quasi-coherent
modules, the functor `M ↦ Mᵃ` is faithful. -/
public theorem faithful_associatedModuleFunctor_of_isPrestack
    (hH : IsPrestackOver S toOver J)
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] :
    (associatedModuleFunctor S toOver).Faithful :=
  faithful_associatedModuleFunctor_of_injective S toOver
    (fun M N _ _ => associatedModuleMap_injective_of_isPrestack S toOver J
      (hH M N inferInstance inferInstance) hcover X₀)

/-- **Descent, Lemma 0GN7 over an arbitrary base, fullness clause, as a property of the functor.**
On a site satisfying the hypotheses of `Stacks.Sites.surjective_associatedModuleMap_of_isPrestack`
for every pair of quasi-coherent modules, the functor `M ↦ Mᵃ` is full. -/
public theorem full_associatedModuleFunctor_of_isPrestack
    (hH : IsPrestackOver S toOver J)
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf J (associatedPresheaf S M toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    (associatedModuleFunctor S toOver).Full :=
  full_associatedModuleFunctor_of_surjective S toOver
    (fun M N _ _ => surjective_associatedModuleMap_of_isPrestack S toOver J
      (hH M N inferInstance inferInstance) (hM N inferInstance) hcover X₀ hterm)

end Functor

end Stacks.Sites

end
