module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelationSheaves
public import StacksFrontier.AlgebraicGeometry.Conormal.AmbientAffine
public import StacksFrontier.AlgebraicGeometry.PartTwo.Restrict

/-!
# The restriction square and the affine square on sections, and the ideal-sheaf side

Let `i : Z ⟶ X` be an immersion of schemes and `V ⊆ X` an affine open whose scheme-theoretic
intersection with `Z` is `Spec (Γ(X, V) ⧸ I)`. [Stacks Project, Tag 01R3] part (2) computes the
sections of `i_* 𝒞_{Z/X}` over `V`; on generators, the class `I.toCotangent a` goes to the
canonical conormal quotient of a section of `ℐ_i` representing `a`. That formula is a composite of
three steps: the restriction square of `i` over `V`, the affine isomorphism square
`V ≅ Spec Γ(X, V)`, and the affine model `Stacks.ClosedImmersion.AffineConormal.conormalΓIso`.
This file computes the restriction square on sections, in the generality of ringed spaces, and the
ideal-sheaf side of the affine square on sections, and assembles the generator formula.

## Main results

* `Stacks.Conormal.affineConormalIsoCotangent_inv_toCotangent_canonical`: the inverse of
  `Stacks.Conormal.affineConormalIsoCotangent` carries the class of `a : I` to the canonical
  conormal quotient of a section of `ℐ_i` over `V` representing `a`.
* `Stacks.Immersion.pushforwardIdealSheafIsoOfSquare_apply_toOpen`: a section of `ℐ_{i ∣_ V}`
  over the top open whose image in `𝒪` is `a : I`, read across the isomorphism square by
  `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare`, is the global section of
  `ℐ_{Spec (Γ(X,V) ⧸ I) ⟶ Spec Γ(X,V)}` determined by `a`.
* `AlgebraicGeometry.RingedSpace.restrictComparison_val_app`: the restriction-of-sections
  comparison of the restriction square, on sections over the open, is a restriction map of the
  sheaf being compared.
* `AlgebraicGeometry.RingedSpace.restrictIdealUnit_val_app`: the ideal-sheaf half of the same
  square on sections, computed down to one restriction of the given section of `ℐ_i`.
* `AlgebraicGeometry.RingedSpace.restrictConormal_val_app_of_eq`: given the morphism-level
  identity of `Stacks.Immersion.canonicalConormalQuotientMap_comp_restrictConormal_eq_unit`, the
  conormal quotient of a section of `ℐ_i` over the open, restricted to the top open of the
  restriction, is the conormal quotient map of the restricted morphism applied to the restricted
  ideal section.
* `RingedSpaceModuleAdjunction.modulePushforwardSquareIso_hom_val_app` and
  `RingedSpaceModuleAdjunction.modulePushforwardSquareIso_inv_val_app`: the pushforward
  comparison of a commuting square of ringed spaces is, on sections, the restriction map along the
  equality of opens that the square's commutativity gives.
* `AlgebraicGeometry.RingedSpace.val_map_unique`: two chains of restriction maps with the same
  source and target agree.

## Implementation notes

The restriction-square lemmas take the trailing morphism (`φ`, `ψ`) and the identities computing
composites as variables; do not write them out or instantiate them with the conormal comparison,
because the kernel then times out unfolding a component of
`AlgebraicGeometry.RingedSpace.restrictPullbackIso`. Where a statement meets the restriction
square, keep the spellings `Z.toSheafedSpace` and `(Opens.map i.toLRSHom.toShHom.hom.base).obj V`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace AlgebraicGeometry.RingedSpace

variable {Zr Xr : RingedSpace.{u, u}}

/-! ### Sections, restriction maps and composition -/

/-- **Two chains of restriction maps with the same source and target agree.** Morphisms between
two fixed opens are unique, so restricting a section along `f` and then along `g` is restricting
it along the unique morphism `k` with the same source and target. -/
theorem val_map_unique (M : SheafOfModules.{u} (structureSheafRing Zr)) {A B C : Opens Zr.carrier}
    (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : M.val.obj (op A)) :
    M.val.map g.op (M.val.map f.op x) = M.val.map k.op x :=
  (M.val.map_comp_apply f.op g.op x).symm.trans
    (M.val.congr_map_apply (congrArg Quiver.Hom.op (Subsingleton.elim (g ≫ f) k)) x)

/-- **Restricting a section along `f` and then back along `g` does nothing.** -/
private theorem val_map_map_self (M : SheafOfModules.{u} (structureSheafRing Zr))
    {A B : Opens Zr.carrier} (f : B ⟶ A) (g : A ⟶ B) (x : M.val.obj (op A)) :
    M.val.map g.op (M.val.map f.op x) = x :=
  (val_map_unique M f g (𝟙 A) x).trans (congr($(M.val.map_id (op A)) x))

/-- **A composite of morphisms of sheaves of modules on a section.** Composition is computed
sectionwise. -/
theorem comp_val_app_apply {M N P : SheafOfModules.{u} (structureSheafRing Zr)}
    (f : M ⟶ N) (g : N ⟶ P) (A : (Opens Zr.carrier)ᵒᵖ) (x : M.val.obj A) :
    (f ≫ g).val.app A x = g.val.app A (f.val.app A x) := rfl

/-- **The pushforward of a morphism of sheaves of modules on a section.** Over an open `A` of the
target it is the given morphism on sections over `f⁻¹A`. -/
theorem modulePushforward_map_val_app (f : Zr ⟶ Xr)
    {M N : SheafOfModules.{u} (structureSheafRing Zr)} (φ : M ⟶ N) (A : Opens Xr.carrier)
    (x : ((modulePushforward f).obj M).val.obj (op A)) :
    ((modulePushforward f).map φ).val.app (op A) x =
      φ.val.app (op ((Opens.map f.hom.base).obj A)) x := rfl

/-- **The image of an open of an open subspace lies in that subspace.** -/
theorem restrictOpensInclusion_obj_le (Xr : RingedSpace.{u, u}) (U : Opens Xr.carrier)
    (A : Opens (Xr.restrict U.isOpenEmbedding).carrier) :
    (restrictOpensInclusion Xr U).obj A ≤ U := by
  rintro x ⟨z, -, rfl⟩
  exact z.2

/-- **The whole of an open subspace lies in the preimage of that subspace.** -/
theorem top_le_opens_map_ofRestrict (Xr : RingedSpace.{u, u}) (U : Opens Xr.carrier) :
    (⊤ : Opens (Xr.restrict U.isOpenEmbedding).carrier) ≤
      (Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U :=
  fun x _ => x.2

/-- **The whole of `Z|_{i⁻¹U}` lies in `(i|_{i⁻¹U})⁻¹(ι_U⁻¹U)`.** -/
theorem top_le_opens_map_restrictHom (i : Zr ⟶ Xr) (U : Opens Xr.carrier) :
    (⊤ : Opens (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) ≤
      (Opens.map (restrictHom i U).hom.base).obj
        ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U) :=
  fun x _ => x.2

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-! ### The pushforward comparison of a square, on sections -/

/-- **Transporting a pushforward along an equality of morphisms of ringed spaces is a restriction
map on sections.** For `p = q` the two opens `p⁻¹A` and `q⁻¹A` are equal, and the transport is
restriction of sections along that equality. -/
theorem eqToHom_modulePushforward_val_app {Zr Xr : RingedSpace.{u, u}} {p q : Zr ⟶ Xr} (h : p = q)
    (N : SheafOfModules.{u} (structureSheafRing Zr)) (A : Opens Xr.carrier)
    (x : ((modulePushforward p).obj N).val.obj (op A)) :
    (eqToHom (congrArg (fun r : Zr ⟶ Xr => (modulePushforward r).obj N) h)).val.app (op A) x =
      N.val.map (eqToHom (congrArg
        (fun r : Zr ⟶ Xr => (Opens.map r.hom.base).obj A) h.symm)).op x := by
  subst h
  exact (congr($(N.val.map_id (op ((Opens.map p.hom.base).obj A))) x)).symm

/-- **`RingedSpaceModuleAdjunction.modulePushforwardSquareIso` on sections.** On sections over
an open `A` of `X₂` the comparison is restriction along the equality
`(j₁ ≫ b)⁻¹A = (a ≫ j₂)⁻¹A`. -/
theorem modulePushforwardSquareIso_hom_val_app (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing Z₁)) (A : Opens X₂.carrier)
    (x : ((modulePushforward b).obj ((modulePushforward j₁).obj N)).val.obj (op A)) :
    ((modulePushforwardSquareIso a b j₁ j₂ comm).hom.app N).val.app (op A) x =
      N.val.map (eqToHom (congrArg
        (fun r : Z₁ ⟶ X₂ => (Opens.map r.hom.base).obj A) comm.symm)).op x :=
  (congr($(modulePushforwardSquareIso_hom_app a b j₁ j₂ comm N).val.app (op A) x)).trans
    (eqToHom_modulePushforward_val_app comm N A x)

/-- **The inverse of `RingedSpaceModuleAdjunction.modulePushforwardSquareIso` on
sections**, the restriction map along the equality of opens read the other way. -/
theorem modulePushforwardSquareIso_inv_val_app (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing Z₁)) (A : Opens X₂.carrier)
    (x : ((modulePushforward j₂).obj ((modulePushforward a).obj N)).val.obj (op A)) :
    ((modulePushforwardSquareIso a b j₁ j₂ comm).inv.app N).val.app (op A) x =
      N.val.map (eqToHom (congrArg
        (fun r : Z₁ ⟶ X₂ => (Opens.map r.hom.base).obj A) comm)).op x :=
  have h1 := (modulePushforwardSquareIso_hom_val_app a b j₁ j₂ comm N A
      (N.val.map (eqToHom (congrArg
        (fun r : Z₁ ⟶ X₂ => (Opens.map r.hom.base).obj A) comm)).op x)).trans
    (val_map_map_self N _ _ x)
  (congrArg _ h1).symm.trans
    congr($((modulePushforwardSquareIso a b j₁ j₂ comm).hom_inv_id_app N).val.app (op A) _)

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

variable {Zr Xr : RingedSpace.{u, u}}

/-! ### The restriction square on sections -/

/-- **The restriction-of-sections comparison of the restriction square, on sections.** Let
`i : Z ⟶ X` be a morphism of ringed spaces, `U` an open of `X` and `V = i⁻¹U`. The canonical
comparison `i_* N ⟶ (ι_U)_*((i|_V)_*(N|_V))` — the unit of `ι_V^* ⊣ (ι_V)_*` pushed forward,
followed by the pushforward comparison of the restriction square and by any morphism `φ` out of
`N|_V` — sends a section of `N` over `i⁻¹U`, read over the top open of the restriction, to `φ` of
the restriction of that section. -/
theorem restrictComparison_val_app (i : Zr ⟶ Xr) (U : Opens Xr.carrier)
    (N : SheafOfModules.{u} (structureSheafRing Zr))
    {P : SheafOfModules.{u}
      (structureSheafRing (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding))}
    (φ : (moduleRestrict Zr ((Opens.map i.hom.base).obj U)).obj N ⟶ P)
    (mm : (⊤ : Opens (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) ⟶
        ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U)))
    (kk : (restrictOpensInclusion Zr ((Opens.map i.hom.base).obj U)).obj ⊤ ⟶
      (Opens.map i.hom.base).obj U)
    (w : ((modulePushforward i).obj N).val.obj (op U)) :
    P.val.map mm.op ((((modulePushforward i).map ((modulePullbackPushforwardAdjunction
        (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N)) ≫
        ((modulePushforwardSquareIso (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
        (Xr.ofRestrict U.isOpenEmbedding) (restrictHom i U) i (restrictHom_comp_ofRestrict i
        U)).inv.app ((modulePullback (Zr.ofRestrict ((Opens.map i.hom.base).obj
        U).isOpenEmbedding)).obj N)) ≫ ((modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map
        ((modulePushforward (restrictHom i U)).map (((modulePullbackRestrictIso Zr ((Opens.map
        i.hom.base).obj U)).hom.app N) ≫ φ)))).val.app (op U) w) =
      φ.val.app (op ⊤) (N.val.map kk.op w) := by
  have e1 : ((modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app N).val.app (op
      ((Opens.map ((Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) ≫ i).hom.base).obj
      U)) (((modulePullbackPushforwardAdjunction (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding)).unit.app N).val.app (op ((Opens.map i.hom.base).obj U)) w) = N.val.map
      ((restrictOpensAdjunction Zr ((Opens.map i.hom.base).obj U)).counit.app ((Opens.map
      i.hom.base).obj U)).op w :=
    congr($(unit_modulePullbackRestrictIso_hom_app Zr ((Opens.map i.hom.base).obj U) N).val.app (op
        ((Opens.map i.hom.base).obj U)) w)
  have e2 : ((modulePushforwardSquareIso (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding) (Xr.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
      (restrictHom_comp_ofRestrict i U)).inv.app ((modulePullback (Zr.ofRestrict ((Opens.map
      i.hom.base).obj U).isOpenEmbedding)).obj N)).val.app (op U)
      (((modulePullbackPushforwardAdjunction (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding)).unit.app N).val.app (op ((Opens.map i.hom.base).obj U)) w) =
      ((modulePullback (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).obj
      N).val.map (eqToHom (congrArg (fun r : (Zr.restrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding) ⟶ Xr => (Opens.map r.hom.base).obj U) (restrictHom_comp_ofRestrict i
      U))).op (((modulePullbackPushforwardAdjunction (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding)).unit.app N).val.app (op ((Opens.map i.hom.base).obj U)) w) :=
    modulePushforwardSquareIso_inv_val_app (Zr.ofRestrict ((Opens.map i.hom.base).obj
        U).isOpenEmbedding) (Xr.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
        (restrictHom_comp_ofRestrict i U) ((modulePullback (Zr.ofRestrict ((Opens.map
        i.hom.base).obj U).isOpenEmbedding)).obj N) U (((modulePullbackPushforwardAdjunction
        (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N).val.app (op
        ((Opens.map i.hom.base).obj U)) w)
  have e3 := PresheafOfModules.naturality_apply ((modulePullbackRestrictIso Zr ((Opens.map
      i.hom.base).obj U)).hom.app N).val (eqToHom (congrArg (fun r : (Zr.restrict ((Opens.map
      i.hom.base).obj U).isOpenEmbedding) ⟶ Xr => (Opens.map r.hom.base).obj U)
      (restrictHom_comp_ofRestrict i U))).op (((modulePullbackPushforwardAdjunction (Zr.ofRestrict
      ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N).val.app (op ((Opens.map
      i.hom.base).obj U)) w)
  have e4 : N.val.map ((restrictOpensInclusion Zr ((Opens.map i.hom.base).obj U)).map (eqToHom
      (congrArg (fun r : (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) ⟶ Xr =>
      (Opens.map r.hom.base).obj U) (restrictHom_comp_ofRestrict i U)))).op (N.val.map
      ((restrictOpensAdjunction Zr ((Opens.map i.hom.base).obj U)).counit.app ((Opens.map
      i.hom.base).obj U)).op w) = N.val.map (homOfLE (restrictOpensInclusion_obj_le Zr ((Opens.map
      i.hom.base).obj U) ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
      U.isOpenEmbedding).hom.base).obj U)))).op w :=
    val_map_unique N ((restrictOpensAdjunction Zr ((Opens.map i.hom.base).obj U)).counit.app
        ((Opens.map i.hom.base).obj U)) ((restrictOpensInclusion Zr ((Opens.map i.hom.base).obj
        U)).map (eqToHom (congrArg (fun r : (Zr.restrict ((Opens.map i.hom.base).obj
        U).isOpenEmbedding) ⟶ Xr => (Opens.map r.hom.base).obj U) (restrictHom_comp_ofRestrict i
        U)))) (homOfLE (restrictOpensInclusion_obj_le Zr ((Opens.map i.hom.base).obj U) ((Opens.map
        (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj
        U)))) w
  have e23 : ((modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app N).val.app (op
      ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
      U.isOpenEmbedding).hom.base).obj U))) (((modulePushforwardSquareIso (Zr.ofRestrict ((Opens.map
      i.hom.base).obj U).isOpenEmbedding) (Xr.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
      (restrictHom_comp_ofRestrict i U)).inv.app ((modulePullback (Zr.ofRestrict ((Opens.map
      i.hom.base).obj U).isOpenEmbedding)).obj N)).val.app (op U)
      (((modulePullbackPushforwardAdjunction (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding)).unit.app N).val.app (op ((Opens.map i.hom.base).obj U)) w)) = N.val.map
      (homOfLE (restrictOpensInclusion_obj_le Zr ((Opens.map i.hom.base).obj U) ((Opens.map
      (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj
      U)))).op w :=
    (congrArg (fun z => ((modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app
        N).val.app (op ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U))) z) e2).trans (e3.trans ((congrArg (fun z =>
        ((moduleRestrict Zr ((Opens.map i.hom.base).obj U)).obj N).val.map (eqToHom (congrArg (fun r
        : (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) ⟶ Xr => (Opens.map
        r.hom.base).obj U) (restrictHom_comp_ofRestrict i U))).op z) e1).trans e4))
  have e5 := PresheafOfModules.naturality_apply φ.val mm.op (N.val.map (homOfLE
      (restrictOpensInclusion_obj_le Zr ((Opens.map i.hom.base).obj U) ((Opens.map (restrictHom i
      U).hom.base).obj ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U)))).op w)
  have e6 : N.val.map ((restrictOpensInclusion Zr ((Opens.map i.hom.base).obj U)).map mm).op
      (N.val.map (homOfLE (restrictOpensInclusion_obj_le Zr ((Opens.map i.hom.base).obj U)
      ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
      U.isOpenEmbedding).hom.base).obj U)))).op w) = N.val.map kk.op w :=
    val_map_unique N (homOfLE (restrictOpensInclusion_obj_le Zr ((Opens.map i.hom.base).obj U)
        ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U)))) ((restrictOpensInclusion Zr ((Opens.map
        i.hom.base).obj U)).map mm) kk w
  exact (congrArg (fun z => P.val.map mm.op (φ.val.app _ z)) e23).trans
    (e5.symm.trans (congrArg _ e6))

/-- **The ideal-sheaf side of the restriction square, on sections.** The unit of
`ι_U^* ⊣ (ι_U)_*` at `ℐ_i`, followed by `(ι_U)_*` of the ideal-sheaf transport
`Stacks.ClosedImmersion.restrictIdealSheafIso` and of the conormal quotient map of `i|_V`, is —
on sections over `U`, read over the top open of the restriction — the conormal quotient map of
`i|_V` applied to the transport of the restriction of the given section of `ℐ_i`. -/
theorem restrictIdealUnit_val_app (i : Zr ⟶ Xr) (U : Opens Xr.carrier)
    (mm : (⊤ : Opens (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) ⟶
        ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U)))
    (kk' : (restrictOpensInclusion Xr U).obj ⊤ ⟶ U)
    (y : (idealSheaf i).val.obj (op U)) :
    (conormalSheaf (restrictHom i U)).val.map mm.op ((((modulePullbackPushforwardAdjunction
        (Xr.ofRestrict U.isOpenEmbedding)).unit.app (idealSheaf i)) ≫ (modulePushforward
        (Xr.ofRestrict U.isOpenEmbedding)).map (((modulePullbackRestrictIso Xr U).hom.app
        (idealSheaf i)) ≫ (restrictIdealSheafIso i U).hom ≫ ((modulePullbackPushforwardAdjunction
        (restrictHom i U)).unit.app (idealSheaf (restrictHom i U))))).val.app (op U) y) =
      ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app (idealSheaf (restrictHom i
          U))).val.app (op ⊤) ((restrictIdealSheafIso i U).hom.val.app (op ⊤) ((idealSheaf
          i).val.map kk'.op y)) := by
  have e1 : ((modulePullbackRestrictIso Xr U).hom.app (idealSheaf i)).val.app
      (op ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U))
      (((modulePullbackPushforwardAdjunction (Xr.ofRestrict U.isOpenEmbedding)).unit.app
        (idealSheaf i)).val.app (op U) y) =
      (idealSheaf i).val.map ((restrictOpensAdjunction Xr U).counit.app U).op y :=
    congr($(unit_modulePullbackRestrictIso_hom_app Xr U (idealSheaf i)).val.app (op U) y)
  have e2 : (idealSheaf i).val.map kk'.op y = ((moduleRestrict Xr U).obj (idealSheaf i)).val.map
      (homOfLE (top_le_opens_map_ofRestrict Xr U)).op ((idealSheaf i).val.map
      ((restrictOpensAdjunction Xr U).counit.app U).op y) :=
    (val_map_unique (idealSheaf i) ((restrictOpensAdjunction Xr U).counit.app U)
        ((restrictOpensInclusion Xr U).map (homOfLE (top_le_opens_map_ofRestrict Xr U))) kk' y).symm
  have e3 := PresheafOfModules.naturality_apply (restrictIdealSheafIso i U).hom.val (homOfLE
      (top_le_opens_map_ofRestrict Xr U)).op ((idealSheaf i).val.map ((restrictOpensAdjunction Xr
      U).counit.app U).op y)
  have e4 := PresheafOfModules.naturality_apply ((modulePullbackPushforwardAdjunction (restrictHom i
      U)).unit.app (idealSheaf (restrictHom i U))).val (homOfLE (top_le_opens_map_ofRestrict Xr
      U)).op ((restrictIdealSheafIso i U).hom.val.app (op ((Opens.map (Xr.ofRestrict
      U.isOpenEmbedding).hom.base).obj U)) ((idealSheaf i).val.map ((restrictOpensAdjunction Xr
      U).counit.app U).op y))
  have e5 : (conormalSheaf (restrictHom i U)).val.map mm.op (((modulePullbackPushforwardAdjunction
      (restrictHom i U)).unit.app (idealSheaf (restrictHom i U))).val.app (op ((Opens.map
      (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U)) ((restrictIdealSheafIso i U).hom.val.app
      (op ((Opens.map (Xr.ofRestrict U.isOpenEmbedding).hom.base).obj U)) ((idealSheaf i).val.map
      ((restrictOpensAdjunction Xr U).counit.app U).op y))) = ((modulePullbackPushforwardAdjunction
      (restrictHom i U)).unit.app (idealSheaf (restrictHom i U))).val.app (op ⊤)
      ((restrictIdealSheafIso i U).hom.val.app (op ⊤) ((idealSheaf i).val.map kk'.op y)) :=
    ((conormalSheaf (restrictHom i U)).val.congr_map_apply (congrArg Quiver.Hom.op
        (Subsingleton.elim mm ((Opens.map (restrictHom i U).hom.base).map (homOfLE
        (top_le_opens_map_ofRestrict Xr U))))) _).trans (e4.symm.trans (congrArg (fun z =>
        ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app (idealSheaf (restrictHom i
        U))).val.app (op ⊤) z) (e3.symm.trans (congrArg (fun z => (restrictIdealSheafIso i
        U).hom.val.app (op ⊤) z) e2.symm))))
  exact (congrArg (fun z => (conormalSheaf (restrictHom i U)).val.map mm.op
    (((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app _).val.app _
      ((restrictIdealSheafIso i U).hom.val.app _ z))) e1).trans e5

/-- **The conormal quotient map across the restriction square, on sections.** Given the
morphism-level identity that a map `c` out of `ℐ_i`, followed by the restriction-of-sections
comparison of the restriction square, is the unit of `ι_U^* ⊣ (ι_U)_*` at `ℐ_i` followed by the
ideal-sheaf transport and the conormal quotient map of `i|_V` — that is, the shape of
`Stacks.Immersion.canonicalConormalQuotientMap_comp_restrictConormal_eq_unit` — the image of a
section `y` of `ℐ_i` over `U` under `c`, restricted to the top open of `Z|_V`, is the conormal
quotient map of `i|_V` applied to the transport of the restriction of `y`. -/
theorem restrictConormal_val_app_of_eq (i : Zr ⟶ Xr) (U : Opens Xr.carrier)
    (N : SheafOfModules.{u} (structureSheafRing Zr))
    (φ : (moduleRestrict Zr ((Opens.map i.hom.base).obj U)).obj N ⟶ (conormalSheaf (restrictHom i
        U)))
    (c : idealSheaf i ⟶ (modulePushforward i).obj N)
    (mm : (⊤ : Opens (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) ⟶
        ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U)))
    (kk : (restrictOpensInclusion Zr ((Opens.map i.hom.base).obj U)).obj ⊤ ⟶
      (Opens.map i.hom.base).obj U)
    (kk' : (restrictOpensInclusion Xr U).obj ⊤ ⟶ U)
    (hρ : c ≫ ((modulePushforward i).map ((modulePullbackPushforwardAdjunction (Zr.ofRestrict
        ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N)) ≫ ((modulePushforwardSquareIso
        (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) (Xr.ofRestrict
        U.isOpenEmbedding) (restrictHom i U) i (restrictHom_comp_ofRestrict i U)).inv.app
        ((modulePullback (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).obj N)) ≫
        ((modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map ((modulePushforward (restrictHom
        i U)).map (((modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app N) ≫ φ)))
        = (((modulePullbackPushforwardAdjunction (Xr.ofRestrict U.isOpenEmbedding)).unit.app
        (idealSheaf i)) ≫ (modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map
        (((modulePullbackRestrictIso Xr U).hom.app (idealSheaf i)) ≫ (restrictIdealSheafIso i U).hom
        ≫ ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app (idealSheaf (restrictHom
        i U)))))) (y : (idealSheaf i).val.obj (op U)) :
    φ.val.app (op ⊤) (N.val.map kk.op (c.val.app (op U) y)) =
      ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app (idealSheaf (restrictHom i
          U))).val.app (op ⊤) ((restrictIdealSheafIso i U).hom.val.app (op ⊤) ((idealSheaf
          i).val.map kk'.op y)) :=
  have hA := restrictComparison_val_app i U N φ mm kk (c.val.app (op U) y)
  have hc := comp_val_app_apply c (((modulePushforward i).map ((modulePullbackPushforwardAdjunction
      (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N)) ≫
      ((modulePushforwardSquareIso (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
      (Xr.ofRestrict U.isOpenEmbedding) (restrictHom i U) i (restrictHom_comp_ofRestrict i
      U)).inv.app ((modulePullback (Zr.ofRestrict ((Opens.map i.hom.base).obj
      U).isOpenEmbedding)).obj N)) ≫ ((modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map
      ((modulePushforward (restrictHom i U)).map (((modulePullbackRestrictIso Zr ((Opens.map
      i.hom.base).obj U)).hom.app N) ≫ φ)))) (op U) y
  have hB := restrictIdealUnit_val_app i U mm kk' y
  hA.symm.trans ((congrArg (fun z => (conormalSheaf (restrictHom i U)).val.map mm.op z)
      (hc.symm.trans (congr($(hρ).val.app (op U) y)))).trans hB)

/-! ### Transporting the restriction square onto the affine square -/

/-- **The restriction of a morphism of sheaves of modules to an open subspace, on sections.** Over
an open `A` of the subspace it is the given morphism on sections over the image of `A`. -/
theorem moduleRestrict_map_val_app (U : Opens Xr.carrier)
    {M N : SheafOfModules.{u} (structureSheafRing Xr)} (ψ : M ⟶ N)
    (A : Opens (Xr.restrict U.isOpenEmbedding).carrier)
    (x : ((moduleRestrict Xr U).obj M).val.obj (op A)) :
    ((moduleRestrict Xr U).map ψ).val.app (op A) x =
      ψ.val.app (op ((restrictOpensInclusion Xr U).obj A)) x := rfl

/-- **Naturality of a morphism of sheaves of modules, on sections.** Restricting a section and
then applying the morphism is applying the morphism and then restricting. -/
theorem val_app_naturality {M N : SheafOfModules.{u} (structureSheafRing Zr)} (f : M ⟶ N)
    {A B : Opens Zr.carrier} (g : B ⟶ A) (x : M.val.obj (op A)) :
    f.val.app (op B) (M.val.map g.op x) = N.val.map g.op (f.val.app (op A) x) :=
  PresheafOfModules.naturality_apply f.val g.op x

/-- **Equal sections restrict to equal sections.** -/
theorem val_map_congr {N : SheafOfModules.{u} (structureSheafRing Zr)} {A B : Opens Zr.carrier}
    (g : B ⟶ A) {w w' : N.val.obj (op A)} (h : w = w') :
    N.val.map g.op w = N.val.map g.op w' := congrArg _ h

/-- **Transporting the ideal sheaf along an equality of morphisms commutes with its inclusion into
the structure sheaf.** -/
theorem eqToHom_idealSheaf_comp_idealSheafι {p q : Zr ⟶ Xr} (h : p = q)
    (hi : idealSheaf p = idealSheaf q) : eqToHom hi ≫ idealSheafι q = idealSheafι p := by
  subst h
  rw [eqToHom_refl]
  exact Category.id_comp _

/-- **Transporting the conormal sheaf along an equality of morphisms commutes with the conormal
quotient map, on global sections.** -/
theorem eqToHom_conormalSheaf_val_app_unit {p q : Zr ⟶ Xr} (h : p = q)
    (hc : conormalSheaf p = conormalSheaf q) (hi : idealSheaf p = idealSheaf q)
    (z : (idealSheaf p).val.obj (op ⊤)) :
    (eqToHom hc).val.app (op ⊤)
        (((modulePullbackPushforwardAdjunction p).unit.app (idealSheaf p)).val.app (op ⊤) z) =
      ((modulePullbackPushforwardAdjunction q).unit.app (idealSheaf q)).val.app (op ⊤)
        ((eqToHom hi).val.app (op ⊤) z) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl]
  rfl

/-- **`AlgebraicGeometry.RingedSpace.restrictConormal_val_app_of_eq`, transported along an equality
of restricted morphisms.** The sectionwise identity of
`AlgebraicGeometry.RingedSpace.restrictConormal_val_app_of_eq`, for a morphism `q` equal to
`AlgebraicGeometry.RingedSpace.restrictHom i U`. -/
theorem restrictConormal_val_app_eqToHom_of_eq (i : Zr ⟶ Xr) (U : Opens Xr.carrier)
    (N : SheafOfModules.{u} (structureSheafRing Zr))
    (φ : (moduleRestrict Zr ((Opens.map i.hom.base).obj U)).obj N ⟶
      conormalSheaf (restrictHom i U))
    {q : (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) ⟶
      (Xr.restrict U.isOpenEmbedding)} (hq : restrictHom i U = q)
    (hc : conormalSheaf (restrictHom i U) = conormalSheaf q)
    (hi : idealSheaf (restrictHom i U) = idealSheaf q)
    (ψ : (moduleRestrict Zr ((Opens.map i.hom.base).obj U)).obj N ⟶ conormalSheaf q)
    (hψ : ψ = φ ≫ eqToHom hc)
    (c : idealSheaf i ⟶ (modulePushforward i).obj N)
    (mm : (⊤ : Opens (Zr.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) ⟶
        ((Opens.map (restrictHom i U).hom.base).obj ((Opens.map (Xr.ofRestrict
        U.isOpenEmbedding).hom.base).obj U)))
    (kk : (restrictOpensInclusion Zr ((Opens.map i.hom.base).obj U)).obj ⊤ ⟶
      (Opens.map i.hom.base).obj U)
    (kk' : (restrictOpensInclusion Xr U).obj ⊤ ⟶ U)
    (hρ : c ≫ ((modulePushforward i).map ((modulePullbackPushforwardAdjunction (Zr.ofRestrict
        ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app N)) ≫ ((modulePushforwardSquareIso
        (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) (Xr.ofRestrict
        U.isOpenEmbedding) (restrictHom i U) i (restrictHom_comp_ofRestrict i U)).inv.app
        ((modulePullback (Zr.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).obj N)) ≫
        ((modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map ((modulePushforward (restrictHom
        i U)).map (((modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app N) ≫ φ)))
        = (((modulePullbackPushforwardAdjunction (Xr.ofRestrict U.isOpenEmbedding)).unit.app
        (idealSheaf i)) ≫ (modulePushforward (Xr.ofRestrict U.isOpenEmbedding)).map
        (((modulePullbackRestrictIso Xr U).hom.app (idealSheaf i)) ≫ (restrictIdealSheafIso i U).hom
        ≫ ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app (idealSheaf (restrictHom
        i U)))))) (y : (idealSheaf i).val.obj (op U)) :
    ψ.val.app (op ⊤) (N.val.map kk.op (c.val.app (op U) y)) =
      ((modulePullbackPushforwardAdjunction q).unit.app (idealSheaf q)).val.app (op ⊤)
        ((eqToHom hi).val.app (op ⊤)
          ((restrictIdealSheafIso i U).hom.val.app (op ⊤) ((idealSheaf i).val.map kk'.op y))) := by
  subst hψ
  exact (comp_val_app_apply φ (eqToHom hc) (op ⊤) (N.val.map kk.op (c.val.app (op U) y))).trans
    ((congrArg (fun z => (eqToHom hc).val.app (op ⊤) z)
        (restrictConormal_val_app_of_eq i U N φ c mm kk kk' hρ y)).trans
      (eqToHom_conormalSheaf_val_app_unit hq hc hi _))

/-- **A twice pushed-forward isomorphism followed by a comparison, on global sections.** If `ψ`
carries `u` to `v`, then `q_* p_* ψ` followed by `β` carries `u` to `β` of `v`, over the top
open. -/
theorem pushforward_mapIso_trans_val_app_top {Z₁ Y₁ W₁ : RingedSpace.{u, u}} (p : Z₁ ⟶ Y₁)
    (q : Y₁ ⟶ W₁) {M N : SheafOfModules.{u} (structureSheafRing Z₁)} (ψ : M ≅ N)
    {P : SheafOfModules.{u} (structureSheafRing W₁)}
    (β : (modulePushforward q).obj ((modulePushforward p).obj N) ≅ P)
    (γ : (modulePushforward q).obj ((modulePushforward p).obj M) ≅ P)
    (hγ : γ = (modulePushforward q).mapIso ((modulePushforward p).mapIso ψ) ≪≫ β)
    (u : M.val.obj (op ⊤)) (v : N.val.obj (op ⊤)) (h : ψ.hom.val.app (op ⊤) u = v) :
    γ.hom.val.app (op ⊤) u = β.hom.val.app (op ⊤) v := by
  subst hγ
  subst h
  rfl

end AlgebraicGeometry.RingedSpace

namespace CategoryTheory.SheafOfModules

/-- **Evaluating an isomorphism of sheaves of modules over an open and restricting scalars, on an
element.** The underlying map is the one the isomorphism has on sections; restriction of scalars
does not change it. -/
theorem restrictScalars_evaluation_mapIso_hom_apply_of_eq {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (W : M ≅ N) (A : Cᵒᵖ) {S : Type u} [Ring S] (g : S →+* ↑(R.obj.obj A))
    (Θ : (ModuleCat.restrictScalars g).obj ((SheafOfModules.evaluation.{u} R A).obj M) ≅
      (ModuleCat.restrictScalars g).obj ((SheafOfModules.evaluation.{u} R A).obj N))
    (hΘ : Θ = (ModuleCat.restrictScalars g).mapIso
      ((SheafOfModules.evaluation.{u} R A).mapIso W))
    (u : (ModuleCat.restrictScalars g).obj ((SheafOfModules.evaluation.{u} R A).obj M))
    (v : N.val.obj A) (hv : W.hom.val.app A u = v) : Θ.hom.hom u = v := by
  subst hΘ
  subst hv
  rfl

/-- **Restricting a section of a sheaf of modules along the identity does nothing**, over an
arbitrary sheaf of rings. -/
theorem val_map_id_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {A : Cᵒᵖ} (x : M.val.obj A) :
    (M.val.map (𝟙 A)).hom x = x := by
  rw [← PresheafOfModules.presheaf_map_apply_coe, M.val.presheaf.map_id]
  rfl

end CategoryTheory.SheafOfModules

namespace Stacks.ClosedImmersion

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ≅ Z₂) (b : X₁ ≅ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-! ### The conormal half of the generator formula -/

/-- **`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare` on a conormal generator.**
The transport of the pushforward conormal sheaf across an isomorphism square carries the image of
a global section `s` of `ℐ_{j₁}` under the conormal quotient map to the image of the transport of
`s` under the conormal quotient map of `j₂`. -/
theorem ambientPushforwardConormalIsoOfSquare_val_app_unit (comm : j₁ ≫ b.hom = a.hom ≫ j₂)
    (s : (idealSheaf j₁).val.obj (op ⊤)) :
    (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom.val.app (op ⊤)
        (((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)).val.app (op ⊤) s) =
      ((modulePullbackPushforwardAdjunction j₂).unit.app (idealSheaf j₂)).val.app (op ⊤)
        ((pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom.val.app (op ⊤) s) :=
  ((comp_val_app_apply ((modulePushforward b.hom).map
        ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)))
      (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom (op ⊤) s).symm.trans
    (congr($(ambientPushforwardConormalIsoOfSquare_comp_unit a b j₁ j₂ comm).val.app
      (op ⊤) s))).trans
    (comp_val_app_apply (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom
      ((modulePullbackPushforwardAdjunction j₂).unit.app (idealSheaf j₂)) (op ⊤) s)

/-- **Transporting a conormal generator across an isomorphism square, on global sections.** Let
`ψ` identify a sheaf of modules `M` on `Z₁` with the conormal sheaf of `j₁`, let `γ` be the
induced comparison of the twice pushed-forward sheaves, and suppose `ψ` carries `u` to the image
of `s` under the conormal quotient map of `j₁`. Then `γ` carries `u` to the image, under the
conormal quotient map of `j₂`, of the transport of `s`. -/
theorem ambientConormalSquare_val_app_generators (comm : j₁ ≫ b.hom = a.hom ≫ j₂)
    {M : SheafOfModules.{u} (structureSheafRing Z₁)} (ψ : M ≅ conormalSheaf j₁)
    (γ : (modulePushforward b.hom).obj ((modulePushforward j₁).obj M) ≅
      (modulePushforward j₂).obj (conormalSheaf j₂))
    (hγ : γ = (modulePushforward b.hom).mapIso ((modulePushforward j₁).mapIso ψ) ≪≫
      ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm)
    (η : idealSheaf j₂ ⟶ (modulePushforward j₂).obj (conormalSheaf j₂))
    (hη : (modulePullbackPushforwardAdjunction j₂).unit.app (idealSheaf j₂) = η)
    (u : M.val.obj (op ⊤)) (s : (idealSheaf j₁).val.obj (op ⊤))
    (h : ψ.hom.val.app (op ⊤) u =
      ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)).val.app (op ⊤) s)
    (t : (idealSheaf j₂).val.obj (op ⊤))
    (ht : (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom.val.app (op ⊤) s = t) :
    γ.hom.val.app (op ⊤) u = η.val.app (op ⊤) t := by
  subst hη
  exact (pushforward_mapIso_trans_val_app_top j₁ b.hom ψ
      (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm) γ hγ u _ h).trans
    ((ambientPushforwardConormalIsoOfSquare_val_app_unit a b j₁ j₂ comm s).trans
      (congrArg (fun z => ((modulePullbackPushforwardAdjunction j₂).unit.app
        (idealSheaf j₂)).val.app (op ⊤) z) ht))

end Stacks.ClosedImmersion

namespace Stacks.Immersion

variable {Z X : Scheme.{u}}

/-! ### The ideal-sheaf side of the affine square -/

/-- **The structure-sheaf map of `V ≅ Spec Γ(X, V)` on global sections.** It is
`AlgebraicGeometry.Scheme.ΓSpecIso` followed by the identification of `Γ(V, ⊤)` with `Γ(X, V)`,
by `AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop`. -/
theorem structureSheafModuleHom_isoSpec_val_app_top (V : X.Opens) (hV : IsAffineOpen V)
    (z : (SheafOfModules.unit (structureSheafRing (Spec Γ(X, V)).toSheafedSpace)).val.obj (op ⊤)) :
    (structureSheafModuleHom (ringedSpaceIso hV.isoSpec).hom).val.app (op ⊤) z =
      V.topIso.inv.hom ((Scheme.ΓSpecIso Γ(X, V)).hom.hom z) := by
  change (hV.isoSpec.hom.appTop).hom z = _
  rw [hV.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop, CommRingCat.hom_comp]
  rfl

/-- **Stacks Project, Tag 01R3 part (2): the ideal-sheaf side of the affine square.** Let
`i : Z ⟶ X` be a morphism of schemes, `V ⊆ X` an affine open and `I ⊆ Γ(X, V)` an ideal cutting
out the scheme-theoretic intersection of `Z` with `V`, compatibly with `V ≅ Spec Γ(X, V)`. Let
`s` be a section of the ideal sheaf of the restricted morphism `i ∣_ V` over the top open whose
image in `𝒪_V` is `a : I`. Then transporting `s` across the isomorphism square by
`Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare` gives the global section of
`ℐ_{Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)}` determined by `a`, namely the image of
`CategoryTheory.tilde.toOpen` of `a` under
`Stacks.ClosedImmersion.AffineConormal.tildeIdealSheafIso`. -/
theorem pushforwardIdealSheafIsoOfSquare_apply_toOpen (i : Z ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I) (a : I)
    {s : (idealSheaf (morphismRestrictShHom i V)).val.obj (op ⊤)}
    (hs : (idealSheafι (morphismRestrictShHom i V)).val.app (op ⊤) s =
      V.topIso.inv.hom (a : Γ(X, V))) :
    (pushforwardIdealSheafIsoOfSquare (isoQuotRestrict i V I e) (isoSpecRestrict V hV)
          (morphismRestrictShHom i V) (quotImmersion Γ(X, V) I).toLRSHom.toShHom
          (morphismRestrictShHom_comp_isoSpecRestrict i V hV I e he)).hom.val.app (op ⊤) s =
      (tildeIdealSheafIso Γ(X, V) I).hom.val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of Γ(X, V) I) ⊤ a) := by
  refine injective_idealSheafι_val_app (quotImmersion Γ(X, V) I).toLRSHom.toShHom ⊤ ?_
  have hR : (idealSheafι (quotImmersion Γ(X, V) I).toLRSHom.toShHom).val.app (op ⊤)
      ((tildeIdealSheafIso Γ(X, V) I).hom.val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of Γ(X, V) I) ⊤ a)) =
      (Scheme.ΓSpecIso Γ(X, V)).inv.hom (a : Γ(X, V)) :=
    (congr($(tildeIdealSheafIso_hom_comp_idealSheafι Γ(X, V) I).val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of Γ(X, V) I) ⊤ a))).trans
        (congr($(tilde.toOpen_map_app (ModuleCat.ofHom I.subtype) ⊤).hom a))
  have hL := congr($(pushforwardIdealSheafIsoOfSquare_hom_comp_ι
    (isoQuotRestrict i V I e) (isoSpecRestrict V hV) (morphismRestrictShHom i V)
    (quotImmersion Γ(X, V) I).toLRSHom.toShHom
    (morphismRestrictShHom_comp_isoSpecRestrict i V hV I e he)).val.app (op ⊤) s)
  rw [hR]
  have hinj : Function.Injective V.topIso.inv.hom :=
    (ConcreteCategory.bijective_of_isIso V.topIso.inv).1
  have h2 := hinj ((structureSheafModuleHom_isoSpec_val_app_top V hV _).symm.trans (hL.trans hs))
  exact (congr($((Scheme.ΓSpecIso Γ(X, V)).hom_inv_id).hom _)).symm.trans
    (congrArg (Scheme.ΓSpecIso Γ(X, V)).inv.hom h2)

/-! ### The generator formula of part (2) -/

/-- **The restriction-square transport of an ideal section, read in the structure sheaf.** Let `y`
be a section of `ℐ_i` over `V`. Transporting it to a global section of the ideal sheaf of the
restricted morphism and including that into the structure sheaf gives the image of `y` under
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem restrictIdealSectionTop_idealSheafι (i : Z ⟶ X) (V : X.Opens)
    (hi : idealSheaf (restrictHom i.toLRSHom.toShHom V) = idealSheaf (morphismRestrictShHom i V))
    (kk' : (restrictOpensInclusion X.toSheafedSpace V).obj ⊤ ⟶ V)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V)) :
    (idealSheafι (morphismRestrictShHom i V)).val.app (op ⊤)
        ((eqToHom hi).val.app (op ⊤)
          ((restrictIdealSheafIso i.toLRSHom.toShHom V).hom.val.app (op ⊤)
            ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y))) =
      V.topIso.inv.hom ((idealSheafι i.toLRSHom.toShHom).val.app (op V) y) :=
  have hA := comp_val_app_apply (eqToHom hi) (idealSheafι (morphismRestrictShHom i V)) (op ⊤)
    ((restrictIdealSheafIso i.toLRSHom.toShHom V).hom.val.app (op ⊤)
      ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y))
  have hB := congr($(eqToHom_idealSheaf_comp_idealSheafι
      (restrictHom_eq_morphismRestrictShHom i V) hi).val.app (op ⊤)
    ((restrictIdealSheafIso i.toLRSHom.toShHom V).hom.val.app (op ⊤)
      ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y)))
  have hC := comp_val_app_apply (restrictIdealSheafIso i.toLRSHom.toShHom V).hom
    (idealSheafι (restrictHom i.toLRSHom.toShHom V)) (op ⊤)
    ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y)
  have hD := congr($(restrictIdealSheafIso_hom_comp_ι i.toLRSHom.toShHom V).val.app (op ⊤)
    ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y))
  have hE := moduleRestrict_map_val_app V (idealSheafι i.toLRSHom.toShHom) ⊤
    ((idealSheaf i.toLRSHom.toShHom).val.map kk'.op y)
  have hF := PresheafOfModules.naturality_apply (idealSheafι i.toLRSHom.toShHom).val kk'.op y
  have hG := (SheafOfModules.unit (structureSheafRing X.toSheafedSpace)).val.congr_map_apply
    (congrArg Quiver.Hom.op (Subsingleton.elim kk' (eqToHom V.ι_image_top)))
    ((idealSheafι i.toLRSHom.toShHom).val.app (op V) y)
  hA.symm.trans (hB.trans (hC.symm.trans (hD.trans (hE.trans (hF.trans hG)))))

/-- **Restriction in the structure sheaf, read as a sheaf of modules, is restriction in the
structure sheaf.** -/
theorem unit_val_map_eq (U V : X.Opens) (hVU : V ≤ U) (z : Γ(X, U)) :
    (SheafOfModules.unit (structureSheafRing X.toSheafedSpace)).val.map (homOfLE hVU).op z =
      (X.presheaf.map (homOfLE hVU).op).hom z := rfl

end Stacks.Immersion

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-! ### The generator formula of part (2), as one equation -/

/-- **Stacks Project, Tag 01R3 part (2): the canonical affine generators, as a single equation.**
Let `i : Z ⟶ X` be an immersion, `U ⊆ X` an affine open whose scheme-theoretic intersection with
`Z` is `Spec (Γ(X, U) ⧸ K)`, and let `y` be a section of `ℐ_i` over `U` whose image in `𝒪_X` is
`a : K`. Then the inverse of `Stacks.Conormal.affineConormalIsoCotangent` carries the class of
`a` in `K/K²` to the image of `y` under the factorization-free conormal quotient map of `i`. -/
theorem affineConormalIsoCotangent_inv_toCotangent_canonical (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U)
    (K : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing K))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) K) (a : K)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op U))
    (hy : (idealSheafι i.toLRSHom.toShHom).val.app (op U) y = (a : Γ(X, U))) :
    (affineConormalIsoCotangent i U hU K e he).inv.hom (K.toCotangent a) =
      (Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op U) y := by
  have hker : RingHom.ker (i.app U).hom = K := by
    rw [Scheme.Hom.app_eq_appLE]
    exact ker_appLE_eq_of_affineModel i U hU K e he
  have ha0 : (i.app U).hom (a : Γ(X, U)) = 0 := RingHom.mem_ker.mp (hker.ge a.2)
  obtain ⟨x, hx⟩ := exists_idealSection_of_ker i U (a : Γ(X, U)) ha0
  have hW : i.coborderRange.ι ⁻¹ᵁ U ≤ i.coborderRange.ι ⁻¹ᵁ U := le_rfl
  have hx' : (i.coborderRange.ι.appLE U (i.coborderRange.ι ⁻¹ᵁ U) hW).hom (a : Γ(X, U)) =
      (idealSheafι i.liftCoborder.toLRSHom.toShHom).val.app
        (op (i.coborderRange.ι ⁻¹ᵁ U)) x := by
    rw [Scheme.Hom.appLE_preimage_self]
    exact hx.symm
  have hEq : i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U) = i ⁻¹ᵁ U :=
    congrArg (fun p : Z ⟶ X => p ⁻¹ᵁ U) i.liftCoborder_ι
  have hTV : i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U) ≤ i ⁻¹ᵁ U := le_of_eq hEq
  have hA2 := Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE i U K a
    i.coborderRange i.liftCoborder i.liftCoborder_ι (i.coborderRange.ι ⁻¹ᵁ U) hW x y hy hx'
    (i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U)) le_rfl hTV
  have hA3 := congrArg
    (fun ψ : idealSheaf i.liftCoborder.toLRSHom.toShHom ⟶ _ =>
      ψ.val.app (op (i.coborderRange.ι ⁻¹ᵁ U)) x)
    (OpenFactorizations.conormalQuotientMap_liftCoborder i)
  have hB := Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_inv_toCotangent_liftCoborder
    i U hU K e he (i.coborderRange.ι ⁻¹ᵁ U) hW a x hx'
  have hinj : Function.Injective ((Stacks.ClosedImmersion.conormalSheaf
      i.liftCoborder.toLRSHom.toShHom).val.map
      (homOfLE hTV).op) := fun w w' h =>
    (val_map_map_self _ (homOfLE hTV) (homOfLE hEq.ge) w).symm.trans
      ((congrArg _ h).trans (val_map_map_self _ _ _ w'))
  exact hinj (hB.trans (hA3.symm.trans
    ((CategoryTheory.SheafOfModules.val_map_id_apply _ _).symm.trans hA2)))

end Stacks.Conormal

end
