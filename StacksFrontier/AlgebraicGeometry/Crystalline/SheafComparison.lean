module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SDerivation

/-!
# Sheaves on the big crystalline site and their comparison maps

Let `(p, (S, I, γ), X)` be a global crystalline situation.  An object `(U, T, δ)` of the big
crystalline category `CRIS(X/S)` restricts to the object `(U ∩ W, W, δ|_W)` over every open `W` of
its ambient scheme `T`, and these restrictions form a functor from the opens of `T` to
`CRIS(X/S)`.  Consequently a presheaf `F` on `CRIS(X/S)` has, for every object `(U, T, δ)`, a
restriction `F_T` on the ambient scheme `T`, namely `F_T(W) = F(U ∩ W, W, δ|_W)`.

A morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)` restricts to a morphism
`(U ∩ f⁻¹W', f⁻¹W', δ|) ⟶ (U' ∩ W', W', δ'|)` over every open `W'` of `T'`, compatibly with
further shrinking of `W'`; applying `F` to these morphisms gives an `f`-map `F_{T'} ⟶ f_* F_T`,
equivalently, by adjunction, the comparison morphism `c_f : f⁻¹F_{T'} ⟶ F_T`.

The structure sheaf of the big crystalline site is `(U, T, δ) ↦ Γ(T, 𝒪_T)`; it is the composite of
the functor taking an object to its ambient scheme with the global sections functor.  Its
restriction to `T` is the presheaf of rings `W ↦ Γ(W, 𝒪_T)`, and for a presheaf of
`𝒪_{X/S}`-modules `M` the restriction `M_T` is a presheaf of modules over it.  Here the `f`-map
above is a morphism of presheaves of rings `𝒪_{T'} ⟶ f_* 𝒪_T`, the `f`-map of modules is a
morphism `M_{T'} ⟶ f_* M_T` of presheaves of modules over `𝒪_{T'}`, and the adjunction between
pullback and pushforward of presheaves of modules turns it into the `𝒪_T`-linear comparison
morphism `c_f : f^* M_{T'} ⟶ M_T`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap` — the restriction of a
  morphism of `CRIS(X/S)` over an open of the ambient scheme of its target, and
  `Thickening.restrictOpenFunctorMap` the resulting natural transformation.
* `Crystalline.GlobalCrystallineSituation.Thickening.restriction` — the restriction `F_T` of a
  presheaf on `CRIS(X/S)` to the ambient scheme of an object.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictionFMap` — the `f`-map
  `F_{T'} ⟶ f_* F_T` associated with a morphism `f` of `CRIS(X/S)`, and
  `Thickening.comparison` the comparison morphism `c_f : f⁻¹F_{T'} ⟶ F_T`.
* `Crystalline.GlobalCrystallineSituation.structureSheaf` — the structure sheaf `𝒪_{X/S}` of the
  big crystalline site, and `Crystalline.GlobalCrystallineSituation.crisRing` the underlying
  presheaf of rings.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestriction` — the restriction `M_T` of
  a presheaf of `𝒪_{X/S}`-modules, `Thickening.moduleFMap` its `f`-map and
  `Thickening.moduleComparison` the `𝒪_T`-linear comparison morphism `c_f : f^* M_{T'} ⟶ M_T`.
* `Crystalline.GlobalCrystallineSituation.Thickening.inverseTargetHom` — the inverse on ambient
  divided power schemes of a morphism of `CRIS(X/S)` whose two components are isomorphisms.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctorImageMap` — the morphisms
  from the restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme to the
  restrictions of the target of an open immersion out of it over the images of those opens, and
  `Thickening.restrictionImageMap` the induced comparison of restricted presheaves.
* `PresheafOfModules.pushforwardAdjunction` — the adjunction between the pushforwards of
  presheaves of modules along two adjoint functors.
* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionImageIso` — the restriction of
  the structure sheaf of the big crystalline site to the ambient scheme of the source of a
  Cartesian open immersion, identified with its restriction to the ambient scheme of the target
  taken over the images of the opens.
* `Crystalline.GlobalCrystallineSituation.Thickening.modulePushforwardAdjunction` — restriction of
  presheaves of modules along the image functor on opens, as a second left adjoint of the direct
  image, and `Thickening.moduleRestrictionImageMap` the transpose of the `f`-map of a presheaf of
  `𝒪_{X/S}`-modules for that adjunction.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.mono_of_mono` — a morphism of `CRIS(X/S)`
  whose two components are monomorphisms is a monomorphism.
* `Crystalline.SchemeThickening.mem_ideal_iff_app_eq_zero` — a section over an open of the ambient
  scheme of a divided power thickening of schemes lies in the divided power ideal exactly when the
  immersion sends it to zero.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_of_isIso_sourceHom_targetHom` — a
  morphism of `CRIS(X/S)` whose two components are isomorphisms is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_restrictOpenMap` — the restriction of a
  Cartesian morphism which is an open immersion on ambient schemes, over an open contained in the
  image of that open immersion, is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.Thickening.exists_comp_eq_restrictOpenLE_image` — a
  morphism out of the restriction of an object to an open of its ambient scheme factors through a
  Cartesian open immersion into its target, over the image of the open where the factorization
  exists.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_comparison` — the comparison morphism
  of an open immersion of `CRIS(X/S)` is an isomorphism, [Stacks, Tag 07IP].
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE_restrictOpenHom` — the
  morphism between the restrictions of an object to two nested opens of its ambient scheme is
  compatible with the structure morphisms of the two restrictions.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_restrictOpenHom` — the
  restriction of a morphism over an open of the ambient scheme of its target is compatible with
  the structure morphisms of the two restricted objects.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_targetHom` — on ambient
  schemes the restriction of a morphism over an open is the restriction of morphisms of schemes.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictionStructureIso` — the restriction of
  the structure sheaf of the big crystalline site to the ambient scheme of an object is the
  structure sheaf of that scheme.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleRestrictionImageMap` — for a
  Cartesian open immersion of `CRIS(X/S)` the restriction of a presheaf of `𝒪_{X/S}`-modules to
  the ambient scheme of the source is the sections of the restriction to the ambient scheme of the
  target over the images of the opens.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparison` — the comparison
  morphism of an open immersion of `CRIS(X/S)` for presheaves of modules is an isomorphism.

## Implementation notes

The restriction of a morphism over an open `W'` of the ambient scheme of its target is obtained
from `Crystalline.GlobalCrystallineSituation.Thickening.pullbackLiftHom`, the factorization of a
morphism of `CRIS(X/S)` through an open immersion: the structure morphism of the restriction of
the target to `W'` is such an open immersion, and the open over which the factorization exists is
the preimage of `W'`.  In particular the divided power compatibility of the restricted morphism is
the one already established there, and no divided power structure is constructed anew.

Both comparison morphisms are produced from the corresponding `f`-map by an adjunction, as in
[Stacks, Tag 008J]: for presheaves of sets by the adjunction between the inverse image and the
direct image of presheaves on a topological space, and for presheaves of modules by the
adjunction between `PresheafOfModules.pullback` and `PresheafOfModules.pushforward` along the
morphism of presheaves of rings `𝒪_{T'} ⟶ f_* 𝒪_T`, the latter being the `f`-map of the structure
sheaf.  The target category of a presheaf on `CRIS(X/S)` is only required to have colimits for
the comparison morphism itself, so the restriction and the `f`-map also apply to the structure
sheaf, which is a presheaf of commutative rings.

For a morphism which is an open immersion on ambient schemes and whose square is Cartesian, the
direct image of presheaves along it is right adjoint not only to the inverse image but also to
restriction along the image functor on opens, and the transpose of the `f`-map for that second
adjunction is, over an open `V` of the ambient scheme of the source, the presheaf applied to the
restriction of the morphism over the image of `V`.  That restricted morphism is an isomorphism of
`CRIS(X/S)` because its two components are: on ambient schemes it is the restriction of an open
immersion over an open inside its image, and on thickened schemes it is then an isomorphism
because the restricted square is Cartesian.  Inverting a morphism of `CRIS(X/S)` whose two
components are isomorphisms needs the inverse morphism of ambient schemes to be compatible with
the divided powers, which holds because the divided power ideal of a thickening is the kernel of
its immersion, so the square formed by the two inverses carries one divided power ideal into the
other.  Identifying the two left adjoints of the direct image then transports the conclusion to
the comparison morphism itself.

The same argument gives the comparison morphism for presheaves of modules.  There the second left
adjoint of the direct image is again a direct image, namely along the image functor on opens,
semilinear over the inverse of the comparison of the restrictions of the structure sheaf, which is
invertible because that comparison is.  That two direct images along adjoint functors are adjoint
holds for any presheaves of rings linked by two morphisms which are mates of one another, and the
two compatibilities required of them are exactly the two identities between the restriction of a
morphism over an open and its restriction over the image of an open established above.

## References

* [Stacks Project, Tag 07IN](https://stacks.math.columbia.edu/tag/07IN)
* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe v v₁ v₂ v₃ u₁ u₂ u₃ u

noncomputable section

namespace PresheafOfModules

/-- **The pushforward of a presheaf of modules is contravariantly functorial in the functor along
which one pushes forward.**  Functors `F : C ⥤ D` and `G : D ⥤ E` and `H : C ⥤ E` with a natural
transformation `η : F ⋙ G ⟶ H`, a presheaf of rings `R` on `E` and a presheaf of `R`-modules `M`
give a morphism from the pushforward of `M` along `H` to the pushforward along `F` of the
pushforward of `M` along `G`, semilinear over the morphism of presheaves of rings induced by
`η`. -/
def pushforwardOfNatTrans {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (η : F ⋙ G ⟶ H)
    (R : Eᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{v} R) :
    (pushforward₀ H R).obj M ⟶
      (pushforward (F := F) (Functor.whiskerRight (NatTrans.op η) R)).obj
        ((pushforward₀ G R).obj M) where
  app X := M.map (η.app X.unop).op
  naturality {X Y} f := by
    ext x
    exact (M.map_comp_apply (H.op.map f) (η.app (unop Y)).op x).symm.trans
      ((M.congr_map_apply (congrArg Quiver.Hom.op (η.naturality f.unop)).symm x).trans
        (M.map_comp_apply (η.app (unop X)).op ((F ⋙ G).op.map f) x))

/-- The component of `pushforwardOfNatTrans η R M` at `X` is the restriction map of `M` along
the component of `η` at `X`. -/
@[simp]
theorem pushforwardOfNatTrans_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (η : F ⋙ G ⟶ H)
    (R : Eᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) :
    (pushforwardOfNatTrans η R M).app X = M.map (η.app X.unop).op := rfl


section Isomorphisms

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The restriction map of a presheaf of modules along an identity acts as the identity.** -/
theorem map_id_apply_self (M : PresheafOfModules.{v} R) {X : Cᵒᵖ} (x : M.obj X) :
    M.map (𝟙 X) x = x := by
  rw [M.map_id]
  rfl

/-- **The restriction map of a presheaf of modules along an isomorphism is bijective.**  Its
inverse is the restriction map along the inverse isomorphism. -/
theorem bijective_map_of_isIso (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (i : X ⟶ Y) [IsIso i] :
    Function.Bijective (M.map i) :=
  Function.bijective_iff_has_inverse.2 ⟨M.map (inv i),
    fun x ↦ ((M.map_comp_apply i (inv i) x).symm.trans
      (M.congr_map_apply (IsIso.hom_inv_id i) x)).trans (M.map_id_apply_self x),
    fun y ↦ ((M.map_comp_apply (inv i) i (U := Y) y).symm.trans
      (M.congr_map_apply (IsIso.inv_hom_id i) y)).trans (M.map_id_apply_self (X := Y) y)⟩

/-- **A morphism of presheaves of modules whose every component is an isomorphism is an
isomorphism.**  The inverse is assembled from the inverses of the components. -/
theorem isIso_of_forall_isIso_app {M N : PresheafOfModules.{v} R} (f : M ⟶ N)
    (h : ∀ X, IsIso (f.app X)) : IsIso f := by
  refine ⟨⟨{ app := fun X ↦ inv (f.app X)
             naturality := fun {X Y} i ↦ ?_ }, ?_, ?_⟩⟩
  · have := h X
    have := h Y
    rw [Functor.map_inv, IsIso.comp_inv_eq, Category.assoc, f.naturality,
      IsIso.inv_hom_id_assoc]
  · ext X
    have := h X
    simp
  · ext X
    have := h X
    simp

end Isomorphisms

section PushforwardAdjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {G : D ⥤ C} {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
  (adj : G ⊣ F) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)

/-- **The unit of the adjunction between the pushforwards of presheaves of modules along two
adjoint functors.**  Over an object `W` it is the restriction map of the presheaf of modules along
the counit of the adjunction of the index categories; it is semilinear over the composite of the
two given morphisms of presheaves of rings by the second compatibility assumption. -/
def pushforwardAdjunctionUnit
    (hφψ : ∀ W : Cᵒᵖ, φ.app W ≫ ψ.app (op (F.obj W.unop)) =
      S.map (adj.counit.app W.unop).op) :
    𝟭 (PresheafOfModules.{v} S) ⟶ pushforward.{v} ψ ⋙ pushforward.{v} φ where
  app N :=
    { app := fun W ↦ ModuleCat.ofHom
        (X := N.obj W) (Y := ((pushforward.{v} ψ ⋙ pushforward.{v} φ).obj N).obj W)
        { toFun := fun x ↦ N.map (adj.counit.app W.unop).op x
          map_add' := fun x y ↦ map_add (N.map (adj.counit.app W.unop).op).hom x y
          map_smul' := fun r x ↦ (N.map_smul (adj.counit.app W.unop).op r x).trans
            (congrArg (fun s ↦ s • N.map (adj.counit.app W.unop).op x)
              (RingHom.congr_fun (congrArg RingCat.Hom.hom (hφψ W)) r).symm) }
      naturality := fun {W W'} f ↦ by
        ext x
        exact (N.map_comp_apply f (adj.counit.app W'.unop).op x).symm.trans
          ((N.congr_map_apply (congrArg Quiver.Hom.op (adj.counit.naturality f.unop)).symm x).trans
            (N.map_comp_apply (adj.counit.app W.unop).op ((F ⋙ G).op.map f) x)) }
  naturality {N N'} α := by
    ext W x
    exact (naturality_apply α (adj.counit.app W.unop).op x).symm

/-- **The counit of the adjunction between the pushforwards of presheaves of modules along two
adjoint functors.**  Over an object `V` it is the restriction map of the presheaf of modules along
the unit of the adjunction of the index categories; it is linear by the first compatibility
assumption. -/
def pushforwardAdjunctionCounit
    (hψφ : ∀ V : Dᵒᵖ, ψ.app V ≫ φ.app (op (G.obj V.unop)) ≫
      R.map (adj.unit.app V.unop).op = 𝟙 (R.obj V)) :
    pushforward.{v} φ ⋙ pushforward.{v} ψ ⟶ 𝟭 (PresheafOfModules.{v} R) where
  app M :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := ((pushforward.{v} φ ⋙ pushforward.{v} ψ).obj M).obj V) (Y := M.obj V)
        { toFun := fun x ↦ M.map (adj.unit.app V.unop).op x
          map_add' := fun x y ↦ map_add (M.map (adj.unit.app V.unop).op).hom x y
          map_smul' := fun r x ↦ (M.map_smul (adj.unit.app V.unop).op _ x).trans
            (congrArg (fun s ↦ s • M.map (adj.unit.app V.unop).op x)
              (RingHom.congr_fun (congrArg RingCat.Hom.hom (hψφ V)) r)) }
      naturality := fun {V V'} i ↦ by
        ext x
        exact (M.map_comp_apply ((G ⋙ F).op.map i) (adj.unit.app V'.unop).op x).symm.trans
          ((M.congr_map_apply (congrArg Quiver.Hom.op (adj.unit.naturality i.unop)).symm x).trans
            (M.map_comp_apply (adj.unit.app V.unop).op i x)) }
  naturality {M M'} α := by
    ext V x
    exact (naturality_apply α (adj.unit.app V.unop).op x).symm

/-- **The pushforwards of presheaves of modules along two adjoint functors are adjoint.**  Let
`adj : G ⊣ F` be an adjunction between `G : D ⥤ C` and `F : C ⥤ D`, let `R` and `S` be presheaves
of rings on `D` and on `C`, and let `φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ S` be morphisms of
presheaves of rings such that the composite of `φ` and `ψ` over an object of `C` is induced by the
counit and the composite of `ψ`, `φ` and the restriction map along the unit over an object of `D`
is the identity.  Then the pushforward along `ψ` is left adjoint to the pushforward along `φ`. -/
def pushforwardAdjunction
    (hφψ : ∀ W : Cᵒᵖ, φ.app W ≫ ψ.app (op (F.obj W.unop)) =
      S.map (adj.counit.app W.unop).op)
    (hψφ : ∀ V : Dᵒᵖ, ψ.app V ≫ φ.app (op (G.obj V.unop)) ≫
      R.map (adj.unit.app V.unop).op = 𝟙 (R.obj V)) :
    pushforward.{v} ψ ⊣ pushforward.{v} φ where
  unit := pushforwardAdjunctionUnit adj φ ψ hφψ
  counit := pushforwardAdjunctionCounit adj φ ψ hψφ
  left_triangle_components N := by
    ext V x
    exact (N.map_comp_apply (adj.counit.app (G.obj V.unop)).op
      (G.map (adj.unit.app V.unop)).op x).symm.trans ((N.congr_map_apply
        (congrArg Quiver.Hom.op (adj.left_triangle_components V.unop)) x).trans
          (N.map_id_apply_self x))
  right_triangle_components M := by
    ext W x
    exact (M.map_comp_apply (F.map (adj.counit.app W.unop)).op
      (adj.unit.app (F.obj W.unop)).op x).symm.trans ((M.congr_map_apply
        (congrArg Quiver.Hom.op (adj.right_triangle_components W.unop)) x).trans
          (M.map_id_apply_self x))

end PushforwardAdjunction

end PresheafOfModules

namespace AlgebraicGeometry

/-- **The restriction of an open immersion over an open contained in its image is an
isomorphism.**  The restriction is the isomorphism onto the image of the preimage of that open,
followed by the inclusion of that image, which is the open itself. -/
theorem isIso_morphismRestrict_of_le_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {U : Y.Opens} (hU : U ≤ f.opensRange) : IsIso (f ∣_ U) := by
  have he : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have : IsIso (Y.homOfLE (f.image_preimage_le U)) :=
    inferInstanceAs (IsIso (Y.isoOfEq he).hom)
  rw [← f.isoImage_preimage_hom_homOfLE U]
  infer_instance

end AlgebraicGeometry

namespace DividedPowers

/-- **A ring homomorphism is a divided power morphism as soon as it becomes one after composition
with an injective divided power morphism.**  Compatibility with the divided powers is an equation
in the final ring, where the two composites agree. -/
theorem IsDPMorphism.of_injective_comp {R T W : Type*} [CommSemiring R] [CommSemiring T]
    [CommSemiring W] {I : Ideal R} {J : Ideal T} {K : Ideal W} (δ : DividedPowers I)
    (ε : DividedPowers J) (ζ : DividedPowers K) (f : R →+* T) (k : T →+* W)
    (hk : Function.Injective k) (hI : Ideal.map f I ≤ J)
    (hkf : IsDPMorphism δ ζ (k.comp f)) (hε : IsDPMorphism ε ζ k) : IsDPMorphism δ ε f where
  ideal_comp := hI
  dpow_comp a ha := hk (by
    rw [hε.map_dpow (hI (Ideal.mem_map_of_mem f ha))]
    exact hkf.dpow_comp a ha)

end DividedPowers

namespace Crystalline.SchemeThickening

/-- **The divided power ideal of a divided power thickening of schemes is detected by its
immersion.**  A section over an open of the ambient scheme lies in the divided power ideal exactly
when the immersion sends it to zero: over an affine open this is the identification of the divided
power ideal with the kernel ideal of the immersion, and both conditions are local. -/
theorem mem_ideal_iff_app_eq_zero (D : SchemeThickening.{u}) (V : D.target.scheme.Opens)
    (s : Γ(D.target.scheme, V)) :
    s ∈ D.target.ideal.obj (op V) ↔ D.immersion.app V s = 0 := by
  have haff : ∀ (W : D.target.scheme.affineOpens) (t : Γ(D.target.scheme, W.1)),
      t ∈ D.target.ideal.obj (op W.1) ↔ D.immersion.app W.1 t = 0 := by
    intro W t
    rw [D.ideal_eq_ker W, Scheme.Hom.ker_apply]
    rfl
  refine ⟨D.immersion_app_eq_zero_of_mem V s, fun hs ↦ D.target.ideal.isSheaf s fun x hx ↦ ?_⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    D.target.scheme.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  refine ⟨W, homOfLE hWV, ?_, hxW⟩
  change D.target.scheme.presheaf.map (homOfLE hWV).op s ∈ D.target.ideal.obj (op W)
  refine (haff ⟨W, hW⟩ _).mpr ?_
  have hnat := ConcreteCategory.congr_hom (D.immersion.naturality (homOfLE hWV).op) s
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
  rw [hnat, hs, map_zero]

/-- **A commuting square of divided power thickenings of schemes carries sections of the divided
power ideal to sections of the divided power ideal.**  The ideals are detected by the immersions,
and the square makes the image of a section killed by one immersion killed by the other. -/
theorem app_mem_ideal_of_square (D E : SchemeThickening.{u})
    (γ : E.target.scheme ⟶ D.target.scheme) (k : E.source ⟶ D.source)
    (h : E.immersion ≫ γ = k ≫ D.immersion) (U : D.target.scheme.Opens)
    {a : Γ(D.target.scheme, U)} (ha : a ∈ D.target.ideal.obj (op U)) :
    γ.app U a ∈ E.target.ideal.obj (op (γ ⁻¹ᵁ U)) := by
  have ha0 := (D.mem_ideal_iff_app_eq_zero U a).mp ha
  have h2 : (k ≫ D.immersion).app U a = 0 := by
    change k.app (D.immersion ⁻¹ᵁ U) (D.immersion.app U a) = 0
    rw [ha0, map_zero]
  have hce := ConcreteCategory.congr_hom (Scheme.Hom.congr_app h U) a
  rw [CommRingCat.comp_apply, h2, map_zero] at hce
  exact (E.mem_ideal_iff_app_eq_zero _ _).mpr hce

/-- **A commuting square of divided power thickenings of schemes carries divided power ideals into
divided power ideals.** -/
theorem map_ideal_le_of_square (D E : SchemeThickening.{u})
    (γ : E.target.scheme ⟶ D.target.scheme) (k : E.source ⟶ D.source)
    (h : E.immersion ≫ γ = k ≫ D.immersion) (U : D.target.scheme.Opens) :
    Ideal.map (γ.app U).hom (D.target.ideal.obj (op U)) ≤
      E.target.ideal.obj (op (γ ⁻¹ᵁ U)) :=
  Ideal.map_le_iff_le_comap.2 fun _ ha ↦ app_mem_ideal_of_square D E γ k h U ha

end Crystalline.SchemeThickening

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

/-- **A morphism of `CRIS(X/S)` whose two components are monomorphisms is a monomorphism.**  A
morphism of `CRIS(X/S)` is determined by its maps on the thickened and on the ambient scheme. -/
theorem mono_of_mono {A B : Thickening S} (f : A ⟶ B) (hs : Mono f.sourceHom)
    (ht : Mono f.targetHom.hom) : Mono f := by
  constructor
  intro Z a b h
  exact Hom.ext ((cancel_mono f.sourceHom).mp (congrArg Hom.sourceHom h))
    (DividedPowerScheme.Hom.ext ((cancel_mono f.targetHom.hom).mp
      (congrArg (fun k ↦ DividedPowerScheme.Hom.hom (Hom.targetHom k)) h)))

variable (A : Thickening S)

/-- **Restricting further is compatible with the structure morphisms.**  Both components of the
structure morphism of a restriction are the open immersions of the open in question. -/
@[reassoc (attr := simp)]
theorem restrictOpenLE_restrictOpenHom {V V' : A.thickening.target.scheme.Opens} (h : V ≤ V') :
    A.restrictOpenLE h ≫ A.restrictOpenHom V' = A.restrictOpenHom V :=
  Hom.ext (Scheme.homOfLE_ι A.thickening.source (A.thickening.immersion.preimage_mono h))
    (DividedPowerScheme.Hom.ext (Scheme.homOfLE_ι A.thickening.target.scheme h))

/-- The structure morphism of a restriction is a monomorphism. -/
instance mono_restrictOpenHom (V : A.thickening.target.scheme.Opens) :
    Mono (A.restrictOpenHom V) :=
  mono_of_mono _ (inferInstanceAs (Mono (A.thickening.immersion ⁻¹ᵁ V).ι))
    (inferInstanceAs (Mono V.ι))

/-- The ambient scheme of a restriction is an open subscheme, so the structure morphism of a
restriction is an open immersion on ambient schemes. -/
instance isOpenImmersion_restrictOpenHom_targetHom (V : A.thickening.target.scheme.Opens) :
    IsOpenImmersion (A.restrictOpenHom V).targetHom.hom :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- The restriction morphism attached to the equality `V ≤ V` is the identity. -/
@[simp]
theorem restrictOpenLE_rfl (V : A.thickening.target.scheme.Opens) :
    A.restrictOpenLE (le_refl V) = 𝟙 _ := by
  rw [← cancel_mono (A.restrictOpenHom V), restrictOpenLE_restrictOpenHom, Category.id_comp]

/-- The restriction morphisms attached to `V ≤ V'` and `V' ≤ V''` compose to the one attached to
`V ≤ V''`. -/
@[reassoc (attr := simp)]
theorem restrictOpenLE_restrictOpenLE {V V' V'' : A.thickening.target.scheme.Opens} (h : V ≤ V')
    (h' : V' ≤ V'') : A.restrictOpenLE h ≫ A.restrictOpenLE h' = A.restrictOpenLE (h.trans h') := by
  rw [← cancel_mono (A.restrictOpenHom V''), Category.assoc, restrictOpenLE_restrictOpenHom,
    restrictOpenLE_restrictOpenHom, restrictOpenLE_restrictOpenHom]

/-- The functor `restrictOpenFunctor` sends an inclusion of opens to the corresponding restriction
morphism `restrictOpenLE`. -/
@[simp]
theorem restrictOpenFunctor_map {V V' : A.thickening.target.scheme.Opens} (i : V ⟶ V') :
    A.restrictOpenFunctor.map i = A.restrictOpenLE (leOfHom i) := rfl

variable {A}

section Map

variable {B : Thickening S} (g : A ⟶ B)

/-- The open of the ambient scheme of the source over which a morphism of `CRIS(X/S)` factors
through the restriction of its target to an open `W` is the preimage of `W`. -/
theorem pullbackOpen_restrictOpenHom (W : B.thickening.target.scheme.Opens) :
    pullbackOpen (B.restrictOpenHom W) g = g.targetHom.hom ⁻¹ᵁ W := by
  change g.targetHom.hom ⁻¹ᵁ W.ι.opensRange = g.targetHom.hom ⁻¹ᵁ W
  rw [Scheme.Opens.opensRange_ι]

/-- **The restriction of a morphism of `CRIS(X/S)` over an open of the ambient scheme of its
target.**  A morphism `f : (U, T, δ) ⟶ (U', T', δ')` and an open `W` of `T'` give the morphism
`(U ∩ f⁻¹W, f⁻¹W, δ|) ⟶ (U' ∩ W, W, δ'|)` obtained by factoring `f` through the open immersion
`(U' ∩ W, W, δ'|) ⟶ (U', T', δ')`. -/
def restrictOpenMap (W : B.thickening.target.scheme.Opens) :
    A.restrictOpen (g.targetHom.hom ⁻¹ᵁ W) ⟶ B.restrictOpen W :=
  A.restrictOpenLE (pullbackOpen_restrictOpenHom g W).ge ≫
    pullbackLiftHom (B.restrictOpenHom W) g (B.isCartesian_restrictOpenHom W)

/-- **The restriction of a morphism over an open of the ambient scheme of its target is compatible
with the structure morphisms of the two restrictions.** -/
@[reassoc (attr := simp)]
theorem restrictOpenMap_restrictOpenHom (W : B.thickening.target.scheme.Opens) :
    restrictOpenMap g W ≫ B.restrictOpenHom W =
      A.restrictOpenHom (g.targetHom.hom ⁻¹ᵁ W) ≫ g := by
  rw [restrictOpenMap, Category.assoc, pullbackLiftHom_comp, restrictOpenLE_restrictOpenHom_assoc]

/-- **On ambient schemes the restriction of a morphism over an open is compatible with the open
immersions of that open and of its preimage.** -/
theorem restrictOpenMap_targetHom_ι (W : B.thickening.target.scheme.Opens) :
    (restrictOpenMap g W).targetHom.hom ≫ W.ι =
      (g.targetHom.hom ⁻¹ᵁ W).ι ≫ g.targetHom.hom :=
  congrArg (fun k ↦ DividedPowerScheme.Hom.hom (Hom.targetHom k))
    (restrictOpenMap_restrictOpenHom g W)

/-- **On ambient schemes the restriction of a morphism over an open is the restriction of
morphisms of schemes.** -/
theorem restrictOpenMap_targetHom (W : B.thickening.target.scheme.Opens) :
    (restrictOpenMap g W).targetHom.hom = g.targetHom.hom ∣_ W :=
  (cancel_mono W.ι).mp
    ((restrictOpenMap_targetHom_ι g W).trans (morphismRestrict_ι g.targetHom.hom W).symm)

/-- **On thickened schemes the restriction of a morphism over an open is the restriction of the
map on thickened schemes.** -/
theorem restrictOpenMap_sourceHom_ι (W : B.thickening.target.scheme.Opens) :
    (restrictOpenMap g W).sourceHom ≫ (B.thickening.immersion ⁻¹ᵁ W).ι =
      (A.thickening.immersion ⁻¹ᵁ (g.targetHom.hom ⁻¹ᵁ W)).ι ≫ g.sourceHom :=
  congrArg Hom.sourceHom (restrictOpenMap_restrictOpenHom g W)

/-- **The restrictions of a morphism over the opens of the ambient scheme of its target are
compatible with further restriction.** -/
theorem restrictOpenLE_restrictOpenMap {V V' : B.thickening.target.scheme.Opens} (h : V ≤ V') :
    A.restrictOpenLE (g.targetHom.hom.preimage_mono h) ≫ restrictOpenMap g V' =
      restrictOpenMap g V ≫ B.restrictOpenLE h := by
  rw [← cancel_mono (B.restrictOpenHom V'), Category.assoc, Category.assoc,
    restrictOpenMap_restrictOpenHom, restrictOpenLE_restrictOpenHom,
    restrictOpenLE_restrictOpenHom_assoc, restrictOpenMap_restrictOpenHom]

/-- **The restrictions of a morphism of `CRIS(X/S)` over the opens of the ambient scheme of its
target**, as a natural transformation of functors from those opens to `CRIS(X/S)`. -/
def restrictOpenFunctorMap :
    Opens.map g.targetHom.hom.base ⋙ A.restrictOpenFunctor ⟶ B.restrictOpenFunctor where
  app W := restrictOpenMap g W
  naturality _ _ i := restrictOpenLE_restrictOpenMap g (leOfHom i)

/-- The component of `restrictOpenFunctorMap g` at an open `W` is `restrictOpenMap g W`. -/
@[simp]
theorem restrictOpenFunctorMap_app (W : B.thickening.target.scheme.Opens) :
    (restrictOpenFunctorMap g).app W = restrictOpenMap g W := rfl

end Map

section Isomorphism

variable {B : Thickening S} (g : A ⟶ B)

/-- **The morphism between the restrictions of an object of `CRIS(X/S)` to two equal opens of its
ambient scheme is an isomorphism.** -/
theorem isIso_restrictOpenLE {V V' : A.thickening.target.scheme.Opens} (h : V ≤ V')
    (he : V' = V) : IsIso (A.restrictOpenLE h) := by
  subst he
  rw [A.restrictOpenLE_rfl]
  infer_instance

/-- **The inverses of the two components of a morphism of `CRIS(X/S)` form a commuting square of
thickenings** when both components are isomorphisms. -/
theorem immersion_comp_inv_targetHom [IsIso g.sourceHom] [IsIso g.targetHom.hom] :
    B.thickening.immersion ≫ inv g.targetHom.hom =
      inv g.sourceHom ≫ A.thickening.immersion := by
  rw [← cancel_epi g.sourceHom, ← Category.assoc, ← g.immersion_naturality]
  simp

/-- **The inverse on ambient divided power schemes of a morphism of `CRIS(X/S)` whose two
components are isomorphisms.**  The inverse morphism of schemes is compatible with the divided
powers because the divided power ideal of a thickening is detected by its immersion, so the square
formed by the two inverses carries one divided power ideal into the other. -/
def inverseTargetHom [IsIso g.sourceHom] [IsIso g.targetHom.hom] :
    B.thickening.target ⟶ A.thickening.target where
  hom := inv g.targetHom.hom
  compatible U := by
    refine DividedPowers.IsDPMorphism.of_injective_comp _ _
      (A.thickening.target.dividedPowers.dividedPowers
        (op (g.targetHom.hom ⁻¹ᵁ (inv g.targetHom.hom ⁻¹ᵁ U)))) _
      (g.targetHom.hom.app (inv g.targetHom.hom ⁻¹ᵁ U)).hom
      (ConcreteCategory.bijective_of_isIso _).injective
      (SchemeThickening.map_ideal_le_of_square A.thickening B.thickening _ _
        (immersion_comp_inv_targetHom g) U) ?_ (g.targetHom.compatible _)
    change DividedPowers.IsDPMorphism
      (A.thickening.target.dividedPowers.dividedPowers (op U))
      (A.thickening.target.dividedPowers.dividedPowers
        (op ((g.targetHom.hom ≫ inv g.targetHom.hom) ⁻¹ᵁ U)))
      ((g.targetHom.hom ≫ inv g.targetHom.hom).app U).hom
    rw [IsIso.hom_inv_id]
    exact (𝟙 A.thickening.target : A.thickening.target ⟶ _).compatible U

/-- The underlying morphism of schemes of `inverseTargetHom g` is the inverse of that of
`g.targetHom`. -/
@[simp]
theorem inverseTargetHom_hom [IsIso g.sourceHom] [IsIso g.targetHom.hom] :
    (inverseTargetHom g).hom = inv g.targetHom.hom := rfl

/-- **A morphism of `CRIS(X/S)` whose two components are isomorphisms is an isomorphism.**  The
inverse is assembled from the inverses of the two components. -/
theorem isIso_of_isIso_sourceHom_targetHom [IsIso g.sourceHom] [IsIso g.targetHom.hom] :
    IsIso g := by
  refine ⟨⟨{ sourceHom := inv g.sourceHom
             targetHom := inverseTargetHom g
             immersion_naturality := immersion_comp_inv_targetHom g
             base_naturality := ?_
             toX_naturality := ?_ }, ?_, ?_⟩⟩
  · refine DividedPowerScheme.Hom.ext ?_
    change inv g.targetHom.hom ≫ A.toBase.hom = B.toBase.hom
    rw [← cancel_epi g.targetHom.hom]
    simpa using (congrArg DividedPowerScheme.Hom.hom g.base_naturality).symm
  · rw [← cancel_epi g.sourceHom]
    simpa using g.toX_naturality.symm
  · exact Hom.ext (IsIso.hom_inv_id _) (DividedPowerScheme.Hom.ext (IsIso.hom_inv_id _))
  · exact Hom.ext (IsIso.inv_hom_id _) (DividedPowerScheme.Hom.ext (IsIso.inv_hom_id _))

/-- **The restriction of a morphism of `CRIS(X/S)` over an open of the ambient scheme of its
target is Cartesian** as soon as the morphism itself is: its square pasted with the Cartesian
square of the restriction of the target is the square of the morphism pasted with the Cartesian
square of the restriction of the source. -/
theorem isCartesian_restrictOpenMap (hg : IsCartesian g)
    (W : B.thickening.target.scheme.Opens) : IsCartesian (restrictOpenMap g W) := by
  have hsrc : (restrictOpenMap g W).sourceHom ≫ (B.restrictOpenHom W).sourceHom =
      (A.restrictOpenHom (g.targetHom.hom ⁻¹ᵁ W)).sourceHom ≫ g.sourceHom :=
    restrictOpenMap_sourceHom_ι g W
  have htgt : (restrictOpenMap g W).targetHom.hom ≫ (B.restrictOpenHom W).targetHom.hom =
      (A.restrictOpenHom (g.targetHom.hom ⁻¹ᵁ W)).targetHom.hom ≫ g.targetHom.hom :=
    restrictOpenMap_targetHom_ι g W
  refine IsPullback.of_right ?_ (restrictOpenMap g W).immersion_naturality.symm
    (B.isCartesian_restrictOpenHom W)
  rw [hsrc, htgt]
  exact (A.isCartesian_restrictOpenHom (g.targetHom.hom ⁻¹ᵁ W)).paste_horiz hg

/-- **The restriction of a Cartesian morphism of `CRIS(X/S)` which is an open immersion on ambient
schemes, over an open contained in the image of that open immersion, is an isomorphism.**  On
ambient schemes it is the restriction of an open immersion over an open inside its image; on
thickened schemes it is then an isomorphism because the restricted square is Cartesian. -/
theorem isIso_restrictOpenMap [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g)
    (W : B.thickening.target.scheme.Opens) (hW : W ≤ g.targetHom.hom.opensRange) :
    IsIso (restrictOpenMap g W) := by
  have ht : IsIso (restrictOpenMap g W).targetHom.hom := by
    rw [restrictOpenMap_targetHom]
    exact isIso_morphismRestrict_of_le_opensRange g.targetHom.hom hW
  have hs : IsIso (restrictOpenMap g W).sourceHom :=
    (isCartesian_restrictOpenMap g hg W).isIso_fst_of_isIso
  exact isIso_of_isIso_sourceHom_targetHom _

/-- **The restrictions of a morphism of `CRIS(X/S)` which is an open immersion on ambient schemes,
over the images of the opens of the ambient scheme of its source, are compatible with shrinking
those opens.** -/
theorem restrictOpenLE_restrictOpenMap_image [IsOpenImmersion g.targetHom.hom]
    {V V' : A.thickening.target.scheme.Opens} (h : V ≤ V') :
    A.restrictOpenLE h ≫ A.restrictOpenLE (g.targetHom.hom.preimage_image_eq V').ge ≫
        restrictOpenMap g (g.targetHom.hom ''ᵁ V') =
      (A.restrictOpenLE (g.targetHom.hom.preimage_image_eq V).ge ≫
          restrictOpenMap g (g.targetHom.hom ''ᵁ V)) ≫
        B.restrictOpenLE (g.targetHom.hom.image_mono h) := by
  rw [← cancel_mono (B.restrictOpenHom (g.targetHom.hom ''ᵁ V'))]
  simp

/-- **The restriction of a morphism of `CRIS(X/S)` which is an open immersion on ambient schemes,
over an open of the ambient scheme of its target, is its restriction over the image of the
preimage of that open, followed by the inclusion of that image.** -/
theorem restrictOpenLE_restrictOpenMap_image_preimage [IsOpenImmersion g.targetHom.hom]
    (W : B.thickening.target.scheme.Opens) :
    (A.restrictOpenLE (g.targetHom.hom.preimage_image_eq (g.targetHom.hom ⁻¹ᵁ W)).ge ≫
          restrictOpenMap g (g.targetHom.hom ''ᵁ (g.targetHom.hom ⁻¹ᵁ W))) ≫
        B.restrictOpenLE (g.targetHom.hom.image_preimage_le W) =
      restrictOpenMap g W := by
  rw [← cancel_mono (B.restrictOpenHom W)]
  simp

/-- **The restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme, mapped to
the restrictions of the target of an open immersion out of it over the images of those opens**, as
a natural transformation of functors from those opens to `CRIS(X/S)`. -/
def restrictOpenFunctorImageMap [IsOpenImmersion g.targetHom.hom] :
    A.restrictOpenFunctor ⟶ g.targetHom.hom.opensFunctor ⋙ B.restrictOpenFunctor where
  app V := A.restrictOpenLE (g.targetHom.hom.preimage_image_eq V).ge ≫
    restrictOpenMap g (g.targetHom.hom ''ᵁ V)
  naturality _ _ i := restrictOpenLE_restrictOpenMap_image g (leOfHom i)

/-- The component of `restrictOpenFunctorImageMap g` at an open `V` is the restriction to the
preimage of the image of `V`, followed by the restriction of `g` over the image of `V`. -/
@[simp]
theorem restrictOpenFunctorImageMap_app [IsOpenImmersion g.targetHom.hom]
    (V : A.thickening.target.scheme.Opens) :
    (restrictOpenFunctorImageMap g).app V =
      A.restrictOpenLE (g.targetHom.hom.preimage_image_eq V).ge ≫
        restrictOpenMap g (g.targetHom.hom ''ᵁ V) := rfl

/-- **The restrictions of an object of `CRIS(X/S)` to the opens of its ambient scheme over which
an open immersion out of it restricts to an isomorphism.** -/
theorem isIso_restrictOpenFunctorImageMap_app [IsOpenImmersion g.targetHom.hom]
    (hg : IsCartesian g) (V : A.thickening.target.scheme.Opens) :
    IsIso ((restrictOpenFunctorImageMap g).app V) :=
  IsIso.comp_isIso' (isIso_restrictOpenLE _ (g.targetHom.hom.preimage_image_eq V))
    (isIso_restrictOpenMap g hg _ (g.targetHom.hom.image_le_opensRange V))

/-- **A morphism out of the restriction of an object of `CRIS(X/S)` to an open `W` of its ambient
scheme factors through a Cartesian open immersion into its target, over the image in `W` of the
open where that factorization exists.**  Over that open the morphism itself factors through the
restriction of its source, which is identified with the restriction of the object to the image. -/
theorem exists_comp_eq_restrictOpenLE_image {C : Thickening S}
    (W : A.thickening.target.scheme.Opens) (r : A.restrictOpen W ⟶ B) (q : C ⟶ B)
    [IsOpenImmersion q.targetHom.hom] (hq : IsCartesian q)
    (hle : (A.restrictOpenHom W).targetHom.hom ''ᵁ pullbackOpen q r ≤ W) :
    ∃ h : A.restrictOpen ((A.restrictOpenHom W).targetHom.hom ''ᵁ pullbackOpen q r) ⟶ C,
      h ≫ q = A.restrictOpenLE hle ≫ r := by
  obtain ⟨e, he⟩ : ∃ e : (A.restrictOpen W).restrictOpen (pullbackOpen q r) ⟶
      A.restrictOpen ((A.restrictOpenHom W).targetHom.hom ''ᵁ pullbackOpen q r),
      e = (A.restrictOpen W).restrictOpenLE
          ((A.restrictOpenHom W).targetHom.hom.preimage_image_eq (pullbackOpen q r)).ge ≫
        restrictOpenMap (A.restrictOpenHom W)
          ((A.restrictOpenHom W).targetHom.hom ''ᵁ pullbackOpen q r) := ⟨_, rfl⟩
  have hiso : IsIso e := by
    rw [he]
    exact IsIso.comp_isIso'
      (isIso_restrictOpenLE (A := A.restrictOpen W) _
        ((A.restrictOpenHom W).targetHom.hom.preimage_image_eq (pullbackOpen q r)))
      (isIso_restrictOpenMap (A.restrictOpenHom W) (A.isCartesian_restrictOpenHom W) _
        ((A.restrictOpenHom W).targetHom.hom.image_le_opensRange (pullbackOpen q r)))
  have key : e ≫ A.restrictOpenLE hle =
      (A.restrictOpen W).restrictOpenHom (pullbackOpen q r) := by
    rw [← cancel_mono (A.restrictOpenHom W), he]
    simp only [Category.assoc, restrictOpenLE_restrictOpenHom,
      restrictOpenMap_restrictOpenHom, restrictOpenLE_restrictOpenHom_assoc]
  have hinv : inv e ≫ (A.restrictOpen W).restrictOpenHom (pullbackOpen q r) =
      A.restrictOpenLE hle := by
    rw [← key, IsIso.inv_hom_id_assoc]
  refine ⟨inv e ≫ pullbackLiftHom q r hq, ?_⟩
  rw [Category.assoc, pullbackLiftHom_comp, ← Category.assoc, hinv]

end Isomorphism

/-- A morphism out of one left adjoint is the canonical isomorphism to another left adjoint
followed by a morphism out of the latter, as soon as they have the same transpose. -/
private theorem eq_leftAdjointUniq_hom_app_comp {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) {X : C} {Y : D}
    (a : F.obj X ⟶ Y) (b : F'.obj X ⟶ Y) (h : adj₂.homEquiv X Y b = adj₁.homEquiv X Y a) :
    a = (adj₁.leftAdjointUniq adj₂).hom.app X ≫ b := by
  refine (adj₁.homEquiv X Y).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact h.symm

section Restriction

variable {𝒜 : Type v} [Category.{u} 𝒜] (F : (Thickening S)ᵒᵖ ⥤ 𝒜)

/-- **The restriction of a presheaf on `CRIS(X/S)` to the ambient scheme of an object.**  Its
sections over an open `W` of the ambient scheme are the sections of the given presheaf over the
restriction of the object to `W`. -/
def restriction (A : Thickening S) : (A.thickening.target.scheme.Opens)ᵒᵖ ⥤ 𝒜 :=
  A.restrictOpenFunctor.op ⋙ F

/-- The sections of `restriction F A` over an open `W` are the sections of `F` over the
restriction of `A` to `W`. -/
@[simp]
theorem restriction_obj (A : Thickening S) (W : A.thickening.target.scheme.Opens) :
    (restriction F A).obj (op W) = F.obj (op (A.restrictOpen W)) := rfl

/-- The restriction map of `restriction F A` along `W ≤ W'` is `F` applied to the restriction
morphism `A.restrictOpenLE`. -/
@[simp]
theorem restriction_map (A : Thickening S) {W W' : A.thickening.target.scheme.Opens}
    (h : W ≤ W') : (restriction F A).map (homOfLE h).op = F.map (A.restrictOpenLE h).op := rfl

/-- **Stacks Project, Tag 07IP.**  The `f`-map from the restriction of a presheaf to the ambient
scheme of the target of a morphism `f` of `CRIS(X/S)` to its restriction to the ambient scheme of
the source: over an open `W` of the target it is the presheaf applied to the restriction of `f`
over `W`. -/
@[stacks 07IP "the f-map assembled from the restriction mappings"]
def restrictionFMap {A B : Thickening S} (g : A ⟶ B) :
    restriction F B ⟶ g.targetHom.hom.base _* restriction F A :=
  Functor.whiskerRight (NatTrans.op (restrictOpenFunctorMap g)) F

/-- The component of `restrictionFMap F g` at `W` is `F` applied to `restrictOpenMap g W`. -/
@[simp]
theorem restrictionFMap_app {A B : Thickening S} (g : A ⟶ B)
    (W : B.thickening.target.scheme.Opens) :
    (restrictionFMap F g).app (op W) = F.map (restrictOpenMap g W).op := rfl

/-- **Stacks Project, Tag 07IP.**  The comparison morphism `c_f : f⁻¹F_{T'} ⟶ F_T` of a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)`, obtained from the `f`-map `F_{T'} ⟶ f_* F_T` by the
adjunction between inverse and direct image. -/
@[stacks 07IP "the comparison map on the big crystalline site, for presheaves"]
def comparison [HasColimits 𝒜] {A B : Thickening S} (g : A ⟶ B) :
    (TopCat.Presheaf.pullback 𝒜 g.targetHom.hom.base).obj (restriction F B) ⟶ restriction F A :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction 𝒜 g.targetHom.hom.base).homEquiv
    (restriction F B) (restriction F A)).symm (restrictionFMap F g)

/-- The `f`-map is recovered from the comparison morphism by the unit of the adjunction between
inverse and direct image. -/
theorem restrictionFMap_eq_comparison [HasColimits 𝒜] {A B : Thickening S} (g : A ⟶ B) :
    restrictionFMap F g =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction 𝒜 g.targetHom.hom.base).homEquiv
        (restriction F B) (restriction F A)) (comparison F g) :=
  (Equiv.apply_symm_apply _ _).symm

/-- **The comparison between the sections of the restriction of a presheaf to the ambient scheme
of the target of an open immersion of `CRIS(X/S)` over the images of opens, and the restriction to
the ambient scheme of the source.**  Over an open `V` of the ambient scheme of the source it is
the presheaf applied to the restriction of the morphism over the image of `V`. -/
def restrictionImageMap {A B : Thickening S} (g : A ⟶ B) [IsOpenImmersion g.targetHom.hom] :
    g.targetHom.hom.opensFunctor.op ⋙ restriction F B ⟶ restriction F A :=
  Functor.whiskerRight (NatTrans.op (restrictOpenFunctorImageMap g)) F

/-- The component of `restrictionImageMap F g` at `V` is `F` applied to the component of
`restrictOpenFunctorImageMap g` at `V`. -/
@[simp]
theorem restrictionImageMap_app {A B : Thickening S} (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (V : (A.thickening.target.scheme.Opens)ᵒᵖ) :
    (restrictionImageMap F g).app V =
      F.map ((restrictOpenFunctorImageMap g).app V.unop).op := rfl

/-- **For a Cartesian open immersion of `CRIS(X/S)`, the restriction of a presheaf to the ambient
scheme of the source is the sections of the restriction to the ambient scheme of the target over
the images of the opens.** -/
theorem isIso_restrictionImageMap {A B : Thickening S} (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) :
    IsIso (restrictionImageMap F g) := by
  have h : ∀ V, IsIso ((restrictionImageMap F g).app V) := fun V ↦ by
    have h0 := isIso_restrictOpenFunctorImageMap_app g hg V.unop
    have h1 : IsIso ((NatTrans.op (restrictOpenFunctorImageMap g)).app V) := isIso_op _
    exact Functor.map_isIso F _
  exact NatIso.isIso_of_isIso_app _

/-- **The comparison morphism of an open immersion of `CRIS(X/S)` is an isomorphism.**  For a
Cartesian morphism `f : (U, T, δ) ⟶ (U', T', δ')` which is an open immersion on ambient schemes,
the restriction `F_T` is the restriction of `F_{T'}` to the open `T` of `T'`, so the comparison
morphism `c_f : f⁻¹F_{T'} ⟶ F_T` is invertible. -/
@[stacks 07IP "the comparison map is an isomorphism for an open immersion"]
theorem isIso_comparison [HasColimits 𝒜] {A B : Thickening S} (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) : IsIso (comparison F g) := by
  have hc : ((Adjunction.op g.targetHom.hom.opensFunctorAdjunction).whiskerLeft 𝒜).homEquiv
      (restriction F B) (restriction F A) (restrictionImageMap F g) = restrictionFMap F g := by
    ext W
    rw [Adjunction.homEquiv_unit, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Adjunction.whiskerLeft_unit_app_app]
    dsimp only [restriction, Functor.comp_map, Functor.op_map, restrictOpenFunctor_map,
      restrictionImageMap, restrictionFMap, Functor.whiskerRight_app, NatTrans.op_app,
      restrictOpenFunctorMap, restrictOpenFunctorImageMap, Functor.op_obj, Opens.map_obj]
    rw [← F.map_comp]
    exact congrArg F.map (CategoryTheory.op_comp.symm.trans
      (congrArg Quiver.Hom.op (restrictOpenLE_restrictOpenMap_image_preimage g W.unop)))
  have he := eq_leftAdjointUniq_hom_app_comp
    (TopCat.Presheaf.pullbackPushforwardAdjunction 𝒜 g.targetHom.hom.base)
    ((Adjunction.op g.targetHom.hom.opensFunctorAdjunction).whiskerLeft 𝒜)
    (comparison F g) (restrictionImageMap F g) (hc.trans (restrictionFMap_eq_comparison F g))
  have := isIso_restrictionImageMap F g hg
  rw [he]
  infer_instance

/-- **The comparison morphism of the structure morphism of a restriction of an object of
`CRIS(X/S)` to an open of its ambient scheme is an isomorphism.**  That structure morphism is a
Cartesian open immersion. -/
theorem isIso_comparison_restrictOpenHom [HasColimits 𝒜] (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    IsIso (comparison F (A.restrictOpenHom V)) :=
  isIso_comparison F _ (A.isCartesian_restrictOpenHom V)

end Restriction

end Thickening

/-- **Stacks Project, Tag 07IQ.**  The structure sheaf `𝒪_{X/S}` of the big crystalline site: it
sends an object `(U, T, δ)` to the ring of global sections `Γ(T, 𝒪_T)`. -/
def structureSheaf (S : GlobalCrystallineSituation.{u}) :
    (Thickening S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (ambient S).op ⋙ Scheme.Γ

/-- The value of `structureSheaf S` at `A` is the ring of global sections of the ambient scheme
of `A`. -/
@[simp]
theorem structureSheaf_obj (A : Thickening S) :
    (structureSheaf S).obj (op A) = Γ(A.thickening.target.scheme, ⊤) := rfl

/-- The map of `structureSheaf S` along `f` is the map on global sections induced by the morphism
of ambient schemes of `f`. -/
@[simp]
theorem structureSheaf_map {A B : Thickening S} (f : A ⟶ B) :
    (structureSheaf S).map f.op = f.targetHom.hom.appTop := rfl

/-- The structure sheaf of the big crystalline site, viewed as a presheaf of rings. -/
abbrev crisRing (S : GlobalCrystallineSituation.{u}) : (Thickening S)ᵒᵖ ⥤ RingCat.{u} :=
  structureSheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}

namespace Thickening

/-- **The identification of the global sections of an open subscheme with the sections of the
structure sheaf over that open is compatible with the inclusions between opens.**  Both sides are
a restriction map of the structure sheaf between the same two opens. -/
theorem appTop_topIso {X : Scheme.{u}} {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) :
    (X.homOfLE (leOfHom i.unop)).appTop ≫ (unop V).topIso.hom =
      (unop U).topIso.hom ≫ X.presheaf.map i := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom, Scheme.Opens.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm.trans
    ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))

/-- **The restriction of the structure sheaf of the big crystalline site to the ambient scheme of
an object is the structure sheaf of that scheme.**  Over an open `W` the former is the ring of
global sections of the open subscheme `W`. -/
def restrictionStructureIso (A : Thickening S) :
    restriction (structureSheaf S) A ≅ A.thickening.target.scheme.presheaf :=
  NatIso.ofComponents (fun W ↦ Scheme.Opens.topIso W.unop) (fun i ↦ appTop_topIso i)

/-- The restriction of the structure sheaf of the big crystalline site, as a presheaf of rings on
the ambient scheme of an object. -/
abbrev ringRestriction (A : Thickening S) : (A.thickening.target.scheme.Opens)ᵒᵖ ⥤ RingCat.{u} :=
  restriction (crisRing S) A

/-- **Stacks Project, Tag 07IQ.**  The restriction of a presheaf of `𝒪_{X/S}`-modules to the
ambient scheme of an object, as a presheaf of modules over the restriction of the structure sheaf:
its sections over an open `W` are the sections of the given presheaf of modules over the
restriction of the object to `W`. -/
def moduleRestriction (M : PresheafOfModules.{u} (crisRing S)) (A : Thickening S) :
    PresheafOfModules.{u} (ringRestriction A) :=
  (PresheafOfModules.pushforward₀ A.restrictOpenFunctor (crisRing S)).obj M

/-- **Stacks Project, Tag 07IQ.**  The `f`-map of a presheaf of `𝒪_{X/S}`-modules along a morphism
`f` of `CRIS(X/S)`: over an open `W` of the ambient scheme of the target it is the given presheaf
of modules applied to the restriction of `f` over `W`, a map semilinear over the `f`-map of the
structure sheaf. -/
def moduleFMap (M : PresheafOfModules.{u} (crisRing S)) {A B : Thickening S} (g : A ⟶ B) :
    moduleRestriction M B ⟶
      (PresheafOfModules.pushforward (F := Opens.map g.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).obj (moduleRestriction M A) :=
  PresheafOfModules.pushforwardOfNatTrans (restrictOpenFunctorMap g) (crisRing S) M

/-- The component of `moduleFMap M g` at an open `W` is the restriction map of `M` along
`restrictOpenMap g W`. -/
@[simp]
theorem moduleFMap_app (M : PresheafOfModules.{u} (crisRing S)) {A B : Thickening S} (g : A ⟶ B)
    (W : (B.thickening.target.scheme.Opens)ᵒᵖ) :
    (moduleFMap M g).app W = M.map (restrictOpenMap g W.unop).op := rfl

/-- **Stacks Project, Tag 07IQ.**  The comparison morphism `c_f : f^* M_{T'} ⟶ M_T` of a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)` and a presheaf of `𝒪_{X/S}`-modules `M`, a map of
`𝒪_T`-modules obtained from the `f`-map `M_{T'} ⟶ f_* M_T` by the adjunction between pullback and
pushforward of presheaves of modules along the `f`-map of the structure sheaf. -/
@[stacks 07IQ "the comparison map for modules on the big crystalline site, for presheaves"]
def moduleComparison (M : PresheafOfModules.{u} (crisRing S)) {A B : Thickening S} (g : A ⟶ B) :
    (PresheafOfModules.pullback (F := Opens.map g.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).obj (moduleRestriction M B) ⟶ moduleRestriction M A :=
  ((PresheafOfModules.pullbackPushforwardAdjunction
    (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction M B)
      (moduleRestriction M A)).symm (moduleFMap M g)

/-- The `f`-map of a presheaf of `𝒪_{X/S}`-modules is recovered from the comparison morphism by
the unit of the adjunction between pullback and pushforward of presheaves of modules. -/
theorem moduleFMap_eq_moduleComparison (M : PresheafOfModules.{u} (crisRing S))
    {A B : Thickening S} (g : A ⟶ B) :
    moduleFMap M g =
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction M B)
          (moduleRestriction M A)) (moduleComparison M g) :=
  (Equiv.apply_symm_apply _ _).symm

section ImageAdjunction

variable {𝒜 : Type v} [Category.{u} 𝒜] {A B : Thickening S}

/-- **The `f`-map of an open immersion of `CRIS(X/S)` over the image of an open of the ambient
scheme of its source, followed by restriction to that open, is the comparison over images.** -/
theorem restrictionFMap_app_image_comp (F : (Thickening S)ᵒᵖ ⥤ 𝒜) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (V : (A.thickening.target.scheme.Opens)ᵒᵖ) :
    (restrictionFMap F g).app (op (g.targetHom.hom ''ᵁ V.unop)) ≫
        (restriction F A).map (g.targetHom.hom.opensFunctorAdjunction.unit.app V.unop).op =
      (restrictionImageMap F g).app V :=
  (F.map_comp (restrictOpenMap g (g.targetHom.hom ''ᵁ V.unop)).op
      (A.restrictOpenLE (g.targetHom.hom.preimage_image_eq V.unop).ge).op).symm.trans
    (congrArg F.map (congrArg Quiver.Hom.op
      (restrictOpenFunctorImageMap_app g V.unop).symm))

/-- **The `f`-map of an open immersion of `CRIS(X/S)` over an open of the ambient scheme of its
target is restriction to the image of the preimage of that open followed by the comparison over
images.** -/
theorem restrictionFMap_app_eq_comp (F : (Thickening S)ᵒᵖ ⥤ 𝒜) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (W : (B.thickening.target.scheme.Opens)ᵒᵖ) :
    (restrictionFMap F g).app W =
      (restriction F B).map (g.targetHom.hom.opensFunctorAdjunction.counit.app W.unop).op ≫
        (restrictionImageMap F g).app (op (g.targetHom.hom ⁻¹ᵁ W.unop)) :=
  (congrArg F.map (congrArg Quiver.Hom.op
      (restrictOpenLE_restrictOpenMap_image_preimage g W.unop).symm)).trans
    (F.map_comp (B.restrictOpenLE (g.targetHom.hom.image_preimage_le W.unop)).op
      ((restrictOpenFunctorImageMap g).app (g.targetHom.hom ⁻¹ᵁ W.unop)).op)

end ImageAdjunction

section ModuleIsomorphism

variable {A B : Thickening S}

/-- **The restriction of the structure sheaf of the big crystalline site to the ambient scheme of
the source of a Cartesian open immersion of `CRIS(X/S)` is its restriction to the ambient scheme
of the target, taken over the images of the opens.** -/
def ringRestrictionImageIso (g : A ⟶ B) [IsOpenImmersion g.targetHom.hom]
    (hg : IsCartesian g) :
    g.targetHom.hom.opensFunctor.op ⋙ ringRestriction B ≅ ringRestriction A :=
  have := isIso_restrictionImageMap (crisRing S) g hg
  asIso (restrictionImageMap (crisRing S) g)

/-- The forward morphism of `ringRestrictionImageIso g hg` is `restrictionImageMap`. -/
@[simp]
theorem ringRestrictionImageIso_hom (g : A ⟶ B) [IsOpenImmersion g.targetHom.hom]
    (hg : IsCartesian g) :
    (ringRestrictionImageIso g hg).hom = restrictionImageMap (crisRing S) g := rfl

/-- **For a Cartesian open immersion of `CRIS(X/S)`, restriction of presheaves of modules along
the image functor on the opens of the ambient schemes is a second left adjoint of the direct
image.** -/
def modulePushforwardAdjunction (g : A ⟶ B) [IsOpenImmersion g.targetHom.hom]
    (hg : IsCartesian g) :
    PresheafOfModules.pushforward (F := g.targetHom.hom.opensFunctor)
        (ringRestrictionImageIso g hg).inv ⊣
      PresheafOfModules.pushforward (F := Opens.map g.targetHom.hom.base)
        (restrictionFMap (crisRing S) g) :=
  PresheafOfModules.pushforwardAdjunction g.targetHom.hom.opensFunctorAdjunction
    (restrictionFMap (crisRing S) g) (ringRestrictionImageIso g hg).inv
    (fun W ↦ by
      rw [restrictionFMap_app_eq_comp (crisRing S) g W, Category.assoc,
        ← ringRestrictionImageIso_hom g hg, Iso.hom_inv_id_app]
      exact Category.comp_id _)
    (fun V ↦ by
      rw [restrictionFMap_app_image_comp (crisRing S) g V, ← ringRestrictionImageIso_hom g hg,
        Iso.inv_hom_id_app])

/-- **The comparison between the sections of the restriction of a presheaf of `𝒪_{X/S}`-modules
to the ambient scheme of the target of an open immersion of `CRIS(X/S)` over the images of opens,
and the restriction to the ambient scheme of the source.**  Over an open `V` of the ambient scheme
of the source it is the presheaf of modules applied to the restriction of the morphism over the
image of `V`. -/
def moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) :
    (PresheafOfModules.pushforward (F := g.targetHom.hom.opensFunctor)
          (ringRestrictionImageIso g hg).inv).obj (moduleRestriction M B) ⟶
      moduleRestriction M A where
  app V := ModuleCat.ofHom
    (X := ((PresheafOfModules.pushforward (F := g.targetHom.hom.opensFunctor)
      (ringRestrictionImageIso g hg).inv).obj (moduleRestriction M B)).obj V)
    (Y := (moduleRestriction M A).obj V)
    { toFun := fun x ↦ M.map ((restrictOpenFunctorImageMap g).app V.unop).op x
      map_add' := fun x y ↦
        map_add (M.map ((restrictOpenFunctorImageMap g).app V.unop).op).hom x y
      map_smul' := fun r x ↦
        (M.map_smul ((restrictOpenFunctorImageMap g).app V.unop).op _ x).trans
          (congrArg (fun s ↦ s • M.map ((restrictOpenFunctorImageMap g).app V.unop).op x)
            (RingHom.congr_fun (congrArg RingCat.Hom.hom
              (Iso.inv_hom_id_app (ringRestrictionImageIso g hg) V)) r)) }
  naturality {V V'} i := by
    ext x
    exact (M.map_comp_apply
          ((g.targetHom.hom.opensFunctor ⋙ B.restrictOpenFunctor).map i.unop).op
          ((restrictOpenFunctorImageMap g).app V'.unop).op x).symm.trans
      ((M.congr_map_apply (congrArg Quiver.Hom.op
            ((restrictOpenFunctorImageMap g).naturality i.unop)).symm x).trans
        (M.map_comp_apply ((restrictOpenFunctorImageMap g).app V.unop).op
          (A.restrictOpenFunctor.map i.unop).op x))

/-- **For a Cartesian open immersion of `CRIS(X/S)`, the restriction of a presheaf of
`𝒪_{X/S}`-modules to the ambient scheme of the source is the sections of the restriction to the
ambient scheme of the target over the images of the opens.** -/
theorem isIso_moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) :
    IsIso (moduleRestrictionImageMap M g hg) := by
  refine PresheafOfModules.isIso_of_forall_isIso_app _ fun V ↦ ?_
  have := isIso_restrictOpenFunctorImageMap_app g hg V.unop
  have : IsIso ((restrictOpenFunctorImageMap g).app V.unop).op := isIso_op _
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (M.bijective_map_of_isIso ((restrictOpenFunctorImageMap g).app V.unop).op)

/-- The `f`-map of a presheaf of `𝒪_{X/S}`-modules along a Cartesian open immersion of
`CRIS(X/S)` is the transpose of the comparison over images for the second adjunction. -/
theorem homEquiv_moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) :
    (modulePushforwardAdjunction g hg).homEquiv (moduleRestriction M B) (moduleRestriction M A)
      (moduleRestrictionImageMap M g hg) = moduleFMap M g := by
  rw [Adjunction.homEquiv_unit]
  ext W x
  exact (M.map_comp_apply (B.restrictOpenFunctor.map
        (g.targetHom.hom.opensFunctorAdjunction.counit.app W.unop)).op
      ((restrictOpenFunctorImageMap g).app (g.targetHom.hom ⁻¹ᵁ W.unop)).op x).symm.trans
    (M.congr_map_apply (congrArg Quiver.Hom.op
      (restrictOpenLE_restrictOpenMap_image_preimage g W.unop)) x)

/-- **The comparison morphism of an open immersion of `CRIS(X/S)` for presheaves of modules is an
isomorphism.**  For a Cartesian morphism `f : (U, T, δ) ⟶ (U', T', δ')` which is an open immersion
on ambient schemes, the restriction `M_T` is the restriction of `M_{T'}` to the open `T` of `T'`,
so the comparison morphism `c_f : f^* M_{T'} ⟶ M_T` is invertible. -/
@[stacks 07IQ "the comparison map for modules is an isomorphism for an open immersion"]
theorem isIso_moduleComparison (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) : IsIso (moduleComparison M g) := by
  have he := eq_leftAdjointUniq_hom_app_comp
    (PresheafOfModules.pullbackPushforwardAdjunction (restrictionFMap (crisRing S) g))
    (modulePushforwardAdjunction g hg) (moduleComparison M g) (moduleRestrictionImageMap M g hg)
    ((homEquiv_moduleRestrictionImageMap M g hg).trans (moduleFMap_eq_moduleComparison M g))
  have := isIso_moduleRestrictionImageMap M g hg
  rw [he]
  infer_instance

end ModuleIsomorphism

end Thickening

end Crystalline.GlobalCrystallineSituation

end

end
