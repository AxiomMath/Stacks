module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePropagation

/-!
# Fullness of `M ↦ Mᵃ` over the affine objects of a site

For a quasi-coherent module `M` on an affine scheme `S` and a site `C` of schemes over `S`
containing an object `X₀` with invertible structure morphism that receives a morphism from every
object, every map `Mᵃ ⟶ Nᵃ` of associated presheaves of modules (Tag 03DU) agrees, over the
objects with affine underlying scheme, with `φᵃ` for some `φ : M ⟶ N`. Combined with
`Stacks.Sites.surjective_associatedModuleMap_of_isAffine` this gives the fullness clause of
Descent, Lemma 0GN7 over an affine base.

## Main results

* `AlgebraicGeometry.Scheme.Modules.hom_ext_of_unit_app_top`: a morphism out of the pullback of a
  quasi-coherent module on an affine scheme is determined by the global sections of its composite
  with the unit of the pullback–pushforward adjunction.
* `Stacks.Sites.unit_comp_pushforward_map_app_top`: that composite, for a morphism of schemes over
  `S`, is computed by the pullback map on sections of Tag 03DS.
* `Stacks.Sites.exists_hom_associatedModuleMap_app_eq_of_isAffine`: every map `Mᵃ ⟶ Nᵃ` agrees
  with some `φᵃ` over the objects with affine underlying scheme.
* `Stacks.Sites.surjective_associatedModuleMap` and
  `Stacks.Sites.bijective_associatedModuleMap`: the map `φ ↦ φᵃ` is surjective, resp. bijective,
  over an affine base.
* `Stacks.Sites.full_associatedModuleFunctor`: the functor `Stacks.Sites.associatedModuleFunctor`
  is full.
* `Stacks.Sites.bijective_associatedModuleMap_affineOver_bot`: bijectivity of `φ ↦ φᵃ` on the
  affine schemes over an affine base with the trivial topology.
* `Stacks.Sites.exists_hom_associatedModuleMap_app_eq_overAffine`: the agreement statement on the
  site of all schemes over an affine base.

## Implementation notes

The hypothesis `hterm`, that every object admits a morphism to `X₀`, cannot be dropped: on a site
with two objects and no arrows between them, whose underlying schemes are unrelated affine schemes
over `S`, the two components of a map `Mᵃ ⟶ Nᵃ` are unconstrained.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Let `Y` be an affine scheme, `P` a quasi-coherent `𝒪_Y`-module, `h : T ⟶ Y` a morphism of
schemes and `G` an `𝒪_T`-module whose pushforward along `h` is quasi-coherent. Then two morphisms
`h⁺ P ⟶ G` whose composites with the unit of the pullback–pushforward adjunction agree on global
sections are equal. -/
public theorem hom_ext_of_unit_app_top {Y T : Scheme.{u}} [IsAffine Y] (h : T ⟶ Y)
    (P : Y.Modules) [P.IsQuasicoherent] (G : T.Modules)
    [((Scheme.Modules.pushforward h).obj G).IsQuasicoherent]
    {χ χ' : (Scheme.Modules.pullback h).obj P ⟶ G}
    (hunit : ∀ m : Γ(P, ⊤),
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app P ≫
        (Scheme.Modules.pushforward h).map χ).app ⊤ m =
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app P ≫
        (Scheme.Modules.pushforward h).map χ').app ⊤ m) :
    χ = χ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv P G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top hunit

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Sites

open _root_.AlgebraicGeometry

/-! ### The unit composite is the pullback map on sections -/

/-- For `g : X ⟶ Y` a morphism of schemes over `S`, a module `F` on `S` and a morphism `χ` out of
the pullback of `F` to `X.left`, composing `χ` with the comparison
`(g.left)⁺ (Y.hom⁺ F) ⟶ X.hom⁺ F` and then with the adjunction unit gives, on global sections, the
action of `χ` after `AlgebraicGeometry.pullbackSectionsMap`. -/
public theorem unit_comp_pushforward_map_app_top {S : Scheme.{u}} (F : S.Modules) {X Y : Over S}
    (g : X ⟶ Y) {G : X.left.Modules} (χ : (Scheme.Modules.pullback X.hom).obj F ⟶ G)
    (m : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
        ((Scheme.Modules.pullback Y.hom).obj F) ≫
      (Scheme.Modules.pushforward g.left).map
        (((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F) ≫ χ)).app ⊤ m =
    χ.app ⊤ (pullbackSectionsMap F g m) := by
  have hunfold : pullbackSectionsMap F g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj F) ≫
        (Scheme.Modules.pushforward g.left).map
          ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F)).app ⊤ ≫
      ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
        (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op := rfl
  rw [hunfold, Scheme.Modules.presheaf_map_top_eq_id g.left _ _]
  rfl

/-! ### The affine-local half of fullness -/

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- Let `S` be an affine scheme, let `toOver : C ⥤ Over S` present a category of schemes over `S`
containing an object `X₀` whose structure morphism to `S` is invertible, and suppose every object
of `C` admits a morphism to `X₀`. Then every map `a : Mᵃ ⟶ Nᵃ` of associated presheaves of modules
agrees, over the objects of the site with affine underlying scheme, with the map induced by some
morphism `φ : M ⟶ N`. -/
public theorem exists_hom_associatedModuleMap_app_eq_of_isAffine [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀))
    (a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver) :
    ∃ φ : M ⟶ N, ∀ X : C, IsAffine (toOver.obj X).left →
      (associatedModuleMap S toOver φ).app (op X) = a.app (op X) := by
  have hT₀ : IsAffine (toOver.obj X₀).left := IsAffine.of_isIso (toOver.obj X₀).hom
  have hex : ∀ (Y : C) [IsAffine (toOver.obj Y).left],
      ∃ ψ : (Scheme.Modules.pullback (toOver.obj Y).hom).obj M ⟶
          (Scheme.Modules.pullback (toOver.obj Y).hom).obj N,
        ∀ y, ψ.app ⊤ y = (a.app (op Y)).hom y := fun Y _ =>
    Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq _
  obtain ⟨ψ₀, hψ₀⟩ := hex X₀
  obtain ⟨φ, hφ⟩ := Functor.Full.map_surjective
    (F := Scheme.Modules.pullback (toOver.obj X₀).hom) ψ₀
  refine ⟨φ, fun X hX => ?_⟩
  obtain ⟨f⟩ := hterm X
  obtain ⟨ψX, hψX⟩ := hex X
  have hnat : ∀ y : Γ((Scheme.Modules.pullback (toOver.obj X₀).hom).obj M, ⊤),
      (associatedModuleMap S toOver φ).app (op X)
          ((associatedModulePresheaf S M toOver).map f.op y) =
        a.app (op X) ((associatedModulePresheaf S M toOver).map f.op y) := by
    intro y
    rw [PresheafOfModules.naturality_apply (associatedModuleMap S toOver φ) f.op y,
      PresheafOfModules.naturality_apply a f.op y]
    have hz : (associatedModuleMap S toOver φ).app (op X₀) y = a.app (op X₀) y := by
      change ((Scheme.Modules.pullback (toOver.obj X₀).hom).map φ).app ⊤ y = _
      rw [hφ, hψ₀]
    rw [hz]
  have hkey : ψX = (Scheme.Modules.pullback (toOver.obj X).hom).map φ := by
    set α := (Scheme.Modules.pullbackComp (toOver.map f).left (toOver.obj X₀).hom).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Over.w (toOver.map f))).hom.app M with hα
    have hiso : IsIso α := by rw [hα]; infer_instance
    refine (cancel_epi α).mp ?_
    refine Scheme.Modules.hom_ext_of_unit_app_top (toOver.map f).left _ _ (fun m => ?_)
    rw [hα, unit_comp_pushforward_map_app_top M (toOver.map f) ψX m,
      unit_comp_pushforward_map_app_top M (toOver.map f)
        ((Scheme.Modules.pullback (toOver.obj X).hom).map φ) m, hψX]
    exact (hnat m).symm
  subst hkey
  exact ModuleCat.hom_ext (LinearMap.ext hψX)

/-! ### The fullness clause and Descent, Lemma 0GN7 over an affine base -/

variable (J : GrothendieckTopology C)

/-- Over an affine base `S`, on a site which contains an object `X₀` with invertible structure
morphism and admitting a morphism from every object, and in which the arrows factoring through an
object with affine underlying scheme cover, the map `φ ↦ φᵃ` is surjective on morphisms of
quasi-coherent modules as soon as `Nᵃ` is a sheaf. -/
public theorem surjective_associatedModuleMap [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  surjective_associatedModuleMap_of_isAffine S toOver J hN hcover
    (exists_hom_associatedModuleMap_app_eq_of_isAffine S toOver X₀ hterm)

/-- Under the hypotheses of `Stacks.Sites.surjective_associatedModuleMap` the map `φ ↦ φᵃ` is
bijective on morphisms of quasi-coherent modules, which is full faithfulness of `M ↦ Mᵃ` at the
pair `(M, N)`. -/
public theorem bijective_associatedModuleMap [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    Function.Bijective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  bijective_associatedModuleMap_of_isAffine S toOver J hN hcover X₀
    (exists_hom_associatedModuleMap_app_eq_of_isAffine S toOver X₀ hterm)

/-- Under the hypotheses of `Stacks.Sites.surjective_associatedModuleMap`, with the sheaf condition
asked of every quasi-coherent module, the functor `Stacks.Sites.associatedModuleFunctor` is full.
-/
public theorem full_associatedModuleFunctor [IsAffine S]
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf J (associatedPresheaf S M toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    (associatedModuleFunctor S toOver).Full := by
  refine ⟨fun {F G} f => ?_⟩
  have := F.property
  have := G.property
  obtain ⟨φ, hφ⟩ := surjective_associatedModuleMap S toOver J (hM G.obj G.property) hcover X₀
    hterm f
  exact ⟨ObjectProperty.homMk φ, hφ⟩

/-! ### Affine schemes over an affine base with the trivial topology -/

/-- Take the site to be the full subcategory of the schemes over an affine `S` whose underlying
scheme is affine, carried by the trivial topology. Then `φ ↦ φᵃ` is bijective on morphisms of
quasi-coherent modules on `S`. -/
public theorem bijective_associatedModuleMap_affineOver_bot (S : Scheme.{u}) [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective fun φ : M ⟶ N =>
      associatedModuleMap S (ObjectProperty.ι (C := Over S) (fun T => IsAffine T.left)) φ :=
  have : IsIso ((ObjectProperty.ι (C := Over S) (fun T => IsAffine T.left)).obj
      ⟨Over.mk (𝟙 S), inferInstanceAs (IsAffine S)⟩).hom := inferInstanceAs (IsIso (𝟙 S))
  bijective_associatedModuleMap S (ObjectProperty.ι (C := Over S) (fun T => IsAffine T.left)) ⊥
    (Presheaf.isSheaf_bot _)
    (coverByImage_isAffine_mem S _ ⊥ (fun Z => Z.property))
    ⟨Over.mk (𝟙 S), inferInstanceAs (IsAffine S)⟩
    (fun Z => ⟨ObjectProperty.homMk (P := fun T : Over S => IsAffine T.left)
      (Over.homMk Z.obj.hom (by simp))⟩)

/-! ### The site of all schemes over an affine base -/

/-- Taking the site to be `CategoryTheory.Over S` itself and `toOver` the identity functor, every
map `a : Mᵃ ⟶ Nᵃ` of associated presheaves of modules agrees, over the schemes over `S` which are
affine, with the map induced by some `φ : M ⟶ N`. -/
public theorem exists_hom_associatedModuleMap_app_eq_overAffine (S : Scheme.{u}) [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : associatedModulePresheaf S M (𝟭 (Over S)) ⟶
      associatedModulePresheaf S N (𝟭 (Over S))) :
    ∃ φ : M ⟶ N, ∀ T : Over S, IsAffine T.left →
      (associatedModuleMap S (𝟭 (Over S)) φ).app (op T) = a.app (op T) :=
  have : IsIso ((𝟭 (Over S)).obj (Over.mk (𝟙 S))).hom := inferInstanceAs (IsIso (𝟙 S))
  exists_hom_associatedModuleMap_app_eq_of_isAffine S (𝟭 (Over S)) (Over.mk (𝟙 S))
    (fun T => ⟨Over.homMk T.hom⟩) a

end Stacks.Sites

end
