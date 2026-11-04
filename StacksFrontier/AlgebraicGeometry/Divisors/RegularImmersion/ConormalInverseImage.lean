module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalAssociatedGraded
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageGradedAlgebra
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageGradedAlgebraIso

/-!
# The associated graded as a direct image of the conormal algebra

Let `i : Z ⟶ X` be an immersion of schemes and let `U ⊆ X` be an open with `i(Z) ⊆ U` and
`i(Z)` closed in `U`, so that `i` factors through `U` as a closed immersion `g = openLift i U`
with ideal sheaf `ℐ = ker g`.  The second identity of [Stacks, Tag 0633] part (1) reads

`𝒞_{Z/X,*} = i^{-1}(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`,

with the *topological* inverse image.  Each homogeneous piece of `⨁ₙ ℐⁿ/ℐⁿ⁺¹` is the direct
image along `g` of the corresponding piece of the conormal algebra, so the degree-`n` piece of
`i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` is `𝒞ⁿ_{Z/X}`; these degreewise identifications are multiplicative and
assemble to an isomorphism of sheaves of graded `i^{-1}𝒪_U`-algebras.

## Main definitions

* `SheafOfModules.GradedAlgebra.pieceIsoOfIso`: the degree-`n` component of an isomorphism of
  sheaves of graded algebras.
* `Stacks.Conormal.grZPieceIsoPushforwardConormal`: the degreewise presentation
  `grⁿ ≅ g_* 𝒞ⁿ_{Z/X}` of the associated graded as a direct image of the conormal algebra.
* `Stacks.Conormal.inverseImageGrPieceIsoConormal`: the degree-`n` piece of
  `i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` is `𝒞ⁿ_{Z/X}`.
* `Stacks.Conormal.inverseImageGrIsoConormal`: the second identity of Tag 0633(1),
  `𝒞_{Z/X,*} = i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`, as sheaves of graded `i^{-1}𝒪_U`-algebras.

## Main results

* `Stacks.Conormal.ker_smul_grZSection_eq_zero`: the kernel of the comorphism annihilates the
  sections of `ℐⁿ/ℐⁿ⁺¹` over every open, `ℐ` being the kernel ideal sheaf.
* `Stacks.Conormal.isIso_unit_app_grZPiece`: the unit `grⁿ ⟶ g_* g^* grⁿ` is an isomorphism in
  every degree.
* `Stacks.Conormal.pushforward_obj_eq_pushforward_restrictScalars`: the scheme direct image
  `g_*` is the composite of restriction of scalars along the structure map with the direct image
  along the inverse-image unit.
* `Stacks.Conormal.grZPieceIsoPushforwardConormal_mul`: the presentation is multiplicative.
* `Stacks.Conormal.inverseImageGrIsoConormal_one`: the isomorphism
  `Stacks.Conormal.inverseImageGrIsoConormal` carries the unit to the unit.
* `Stacks.Conormal.conormalAlgebra_identifications`: both identities of Tag 0633 (1) as unital
  isomorphisms of sheaves of graded algebras.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- The degree-`n` component `A.piece n ≅ B.piece n` of an isomorphism `A ≅ B` of sheaves of
graded algebras. -/
def pieceIsoOfIso (e : A ≅ B) (n : ℤ) : A.piece n ≅ B.piece n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := congrArg (fun φ : A ⟶ A => φ.app n) e.hom_inv_id
  inv_hom_id := congrArg (fun φ : B ⟶ B => φ.app n) e.inv_hom_id

/-- The forward map of `pieceIsoOfIso e n` is the degree-`n` component of `e.hom`. -/
@[simp] theorem pieceIsoOfIso_hom (e : A ≅ B) (n : ℤ) :
    (pieceIsoOfIso e n).hom = e.hom.app n := rfl

/-- The inverse map of `pieceIsoOfIso e n` is the degree-`n` component of `e.inv`. -/
@[simp] theorem pieceIsoOfIso_inv (e : A ≅ B) (n : ℤ) :
    (pieceIsoOfIso e n).inv = e.inv.app n := rfl

end SheafOfModules.GradedAlgebra

namespace Stacks.Conormal

/-! ### The kernel ideal annihilates the associated graded over every open -/

section Annihilation

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [QuasiCompact f]

/-- **The kernel of the comorphism annihilates the sections of `ℐⁿ/ℐⁿ⁺¹` over an arbitrary
open**, `ℐ = ker f` being the kernel ideal sheaf of `f`. -/
theorem ker_smul_grSection_eq_zero (n : ℕ) (W : X.Opens) (a : Γ(X, W))
    (ha : (f.app W).hom a = 0) (m : Γ(grPiece f.ker n, W)) : a • m = 0 := by
  classical
  refine TopCat.Presheaf.IsSheaf.section_ext (grPiece f.ker n).isSheaf (U := op W)
    fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  refine ⟨V, hVW, hxV, ?_⟩
  have happ : (f.app V).hom (X.presheaf.map (homOfLE hVW).op a) = 0 := by
    have h := congrArg (fun φ : Γ(X, W) ⟶ Γ(Z, f ⁻¹ᵁ V) => CommRingCat.Hom.hom φ a)
      (f.naturality (homOfLE hVW).op)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero] using h
  have hmem : X.presheaf.map (homOfLE hVW).op a ∈ f.ker.ideal ⟨V, hV⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact RingHom.mem_ker.mpr happ
  have hzero : X.presheaf.map (homOfLE hVW).op a •
      (grPiece f.ker n).presheaf.map (homOfLE hVW).op m = 0 := by
    have hsmul := Submodule.smul_mem_smul
      (N := (⊤ : Submodule Γ(X, V) Γ(grPiece f.ker n, V))) hmem
      (Submodule.mem_top (x := (grPiece f.ker n).presheaf.map (homOfLE hVW).op m))
    rw [smul_top_eq_bot_grSection f.ker n ⟨V, hV⟩] at hsmul
    exact (Submodule.mem_bot _).1 hsmul
  calc (grPiece f.ker n).presheaf.map (homOfLE hVW).op (a • m)
      = X.presheaf.map (homOfLE hVW).op a •
          (grPiece f.ker n).presheaf.map (homOfLE hVW).op m :=
        (grPiece f.ker n).map_smul (homOfLE hVW) a m
    _ = 0 := hzero
    _ = (grPiece f.ker n).presheaf.map (homOfLE hVW).op 0 := by simp

/-- The kernel of the comorphism annihilates the sections of the degree-`n` piece of the
associated graded over every open, for every integer `n`. -/
theorem ker_smul_grZSection_eq_zero (n : ℤ) (W : X.Opens) (a : Γ(X, W))
    (ha : (f.app W).hom a = 0) (m : Γ(grZPiece f.ker n, W)) : a • m = 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · exact grZPiece_section_eq_zero f.ker hn (op W) (a • m)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact ker_smul_grSection_eq_zero f k W a ha m

/-- For a closed immersion `f` with kernel ideal sheaf `ℐ`, the unit `grⁿ ⟶ f_* f^* grⁿ` is an
isomorphism in every degree. -/
theorem isIso_unit_app_grZPiece [IsClosedImmersion f] (n : ℤ) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (grZPiece f.ker n)) :=
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero f (grZPiece f.ker n)
    fun W a ha m => ker_smul_grZSection_eq_zero f n W a ha m

/-- The isomorphism `grⁿ ≅ f_* f^* grⁿ` given by the unit of `f^* ⊣ f_*`. -/
def grZPieceIsoPushforwardPullback [IsClosedImmersion f] (n : ℤ) :
    grZPiece f.ker n ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj (grZPiece f.ker n)) :=
  haveI := isIso_unit_app_grZPiece f n
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (grZPiece f.ker n))

end Annihilation

/-! ### The associated graded as a direct image of the conormal algebra -/

section Presentation

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
  (hsub : Set.range i.base ⊆ (U : Set X))

include hsub

open AlgebraicGeometry.SheafOfModules (inverseImageRingHom underlyingRingHomOfSite
  inverseImageGradedAlgebra inverseImageGradedAlgebraPieceIsoRestrictScalars)
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageMiddleRing)

/-- The structure map `g⁻¹𝒪_U ⟶ 𝒪_Z` of the closed immersion `g = openLift i U hsub`. -/
abbrev openStructureMap :=
  underlyingRingHomOfSite
    (O := inverseImageMiddleRing (openLift i U hsub).toLRSHom.toShHom) (O' := Z.sheaf)
    (ringedSpaceStructureMap (openLift i U hsub).toLRSHom.toShHom)

omit [IsImmersion i] in
/-- The direct image along `g` is restriction of scalars along the structure map followed by the
direct image along the inverse-image unit. -/
theorem pushforward_obj_eq_pushforward_restrictScalars (M : Z.Modules) :
    (Scheme.Modules.pushforward (openLift i U hsub)).obj M =
      (SheafOfModules.pushforward
          (inverseImageRingHom (openLift i U hsub).base (U.toScheme).sheaf)).obj
        ((SheafOfModules.restrictScalars (openStructureMap i U hsub)).obj M) :=
  congrArg (fun F : Z.Modules ⥤ _ => F.obj M)
    (RingedSpaceModuleAdjunction.modulePushforward_eq (openLift i U hsub).toLRSHom.toShHom)

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))

include hcl

/-- **The degreewise presentation of the associated graded as a direct image of the conormal
algebra**: `ℐⁿ/ℐⁿ⁺¹ ≅ g_* 𝒞ⁿ_{Z/X}`, where `g = openLift i U hsub` is the closed immersion
`Z ⟶ U` through which `i` factors and `ℐ = ker g` is the ideal sheaf of `i(Z) ⊂ U`. -/
def grZPieceIsoPushforwardConormal (n : ℤ) :
    (grGradedAlgebra (openIdeal i U hsub)).piece n ≅
      (Scheme.Modules.pushforward (openLift i U hsub)).obj
        ((conormalAlgebra i).algebra.piece n) :=
  haveI := isClosedImmersion_openLift i U hsub hcl
  grZPieceIsoPushforwardPullback (openLift i U hsub) n ≪≫
    (Scheme.Modules.pushforward (openLift i U hsub)).mapIso
      (SheafOfModules.GradedAlgebra.pieceIsoOfIso (conormalIsoGrPullback i U hsub hcl) n).symm

/-! ### The topological inverse image of the associated graded -/

/-- The degree-`n` piece of the topological inverse image `i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` is the
degree-`n` piece `𝒞ⁿ_{Z/X}` of the conormal algebra, read as a sheaf of `i^{-1}𝒪_U`-modules
along the structure map. -/
def inverseImageGrPieceIsoConormal (n : ℤ) :
    (inverseImageGradedAlgebra (openLift i U hsub).base (U.toScheme).sheaf
        (grGradedAlgebra (openIdeal i U hsub))).piece n ≅
      (SheafOfModules.restrictScalars (openStructureMap i U hsub)).obj
        ((conormalAlgebra i).algebra.piece n) :=
  haveI := isClosedImmersion_openLift i U hsub hcl
  inverseImageGradedAlgebraPieceIsoRestrictScalars _ _ _
    (IsClosedImmersion.isClosedEmbedding (openLift i U hsub)).isInducing
    (openStructureMap i U hsub) (fun n => (conormalAlgebra i).algebra.piece n)
    (fun n => (grZPieceIsoPushforwardConormal i U hsub hcl n).trans
      (eqToIso (pushforward_obj_eq_pushforward_restrictScalars i U hsub _))) n

/-! ### The second identity as sheaves of graded algebras -/

/-- The presentation `ℐⁿ/ℐⁿ⁺¹ ≅ g_* 𝒞ⁿ_{Z/X}` on local sections: the unit of `g^* ⊣ g_*`
followed by the inverse of `Stacks.Conormal.conormalIsoGrPullback`. -/
theorem grZPieceIsoPushforwardConormal_hom_app (n : ℤ) (V : (U : Scheme.{u}).Opens)
    (x : ((grGradedAlgebra (openIdeal i U hsub)).piece n).val.obj (op V)) :
    (grZPieceIsoPushforwardConormal i U hsub hcl n).hom.val.app (op V) x =
      ((conormalIsoGrPullback i U hsub hcl).inv.app n).val.app (op (openLift i U hsub ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection (openLift i U hsub)
          ((grGradedAlgebra (openIdeal i U hsub)).piece n) V _ le_rfl x) :=
  Eq.trans rfl (congrArg (((conormalIsoGrPullback i U hsub hcl).inv.app n).val.app
    (op (openLift i U hsub ⁻¹ᵁ V))) (pullbackSection_self (openLift i U hsub)
      ((grGradedAlgebra (openIdeal i U hsub)).piece n) V x)).symm

/-- **The presentation `ℐⁿ/ℐⁿ⁺¹ ≅ g_* 𝒞ⁿ_{Z/X}` is multiplicative**: it carries the product of
the associated graded algebra to the product of the conormal algebra. -/
theorem grZPieceIsoPushforwardConormal_mul (p q : ℤ) (V : (U : Scheme.{u}).Opens)
    (a : ((grGradedAlgebra (openIdeal i U hsub)).piece p).val.obj (op V))
    (b : ((grGradedAlgebra (openIdeal i U hsub)).piece q).val.obj (op V)) :
    (grZPieceIsoPushforwardConormal i U hsub hcl (p + q)).hom.val.app (op V)
        (((grGradedAlgebra (openIdeal i U hsub)).mul p q).app (op V) a b) =
      ((conormalAlgebra i).algebra.mul p q).app (op (openLift i U hsub ⁻¹ᵁ V))
        ((grZPieceIsoPushforwardConormal i U hsub hcl p).hom.val.app (op V) a)
        ((grZPieceIsoPushforwardConormal i U hsub hcl q).hom.val.app (op V) b) := by
  rw [grZPieceIsoPushforwardConormal_hom_app, grZPieceIsoPushforwardConormal_hom_app,
    grZPieceIsoPushforwardConormal_hom_app]
  exact (congrArg (((conormalIsoGrPullback i U hsub hcl).inv.app (p + q)).val.app
      (op (openLift i U hsub ⁻¹ᵁ V)))
      (gradedPullback_mul_pullbackSection (openLift i U hsub)
        (grGradedAlgebra (openIdeal i U hsub)) p q V a b).symm).trans
    ((conormalIsoGrPullback i U hsub hcl).inv.map_mul p q (op (openLift i U hsub ⁻¹ᵁ V)) _ _)

/-- **`𝒞_{Z/X,*} = i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` as sheaves of graded algebras.**  Let `i : Z ⟶ X` be an
immersion, `U ⊆ X` an open with `i(Z) ⊆ U` closed in `U`, and `ℐ ⊆ 𝒪_U` the ideal sheaf of the
closed subscheme `i(Z) ⊂ U`.  Then the topological inverse image `i^{-1}(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`, a
sheaf of graded `i^{-1}𝒪_U`-algebras, is the conormal algebra of `i`, read over `i^{-1}𝒪_U`
along the structure map `i^{-1}𝒪_U ⟶ 𝒪_Z`. -/
def inverseImageGrIsoConormal :
    inverseImageGradedAlgebra (openLift i U hsub).base (U.toScheme).sheaf
        (grGradedAlgebra (openIdeal i U hsub)) ≅
      SheafOfModules.GradedAlgebra.scalarRestrict (openStructureMap i U hsub)
        (conormalAlgebra i).algebra :=
  haveI := isClosedImmersion_openLift i U hsub hcl
  AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebraIsoScalarRestrict _ _ _
    (IsClosedImmersion.isClosedEmbedding (openLift i U hsub)).isInducing
    (openStructureMap i U hsub) (conormalAlgebra i).algebra
    (fun n => (grZPieceIsoPushforwardConormal i U hsub hcl n).trans
      (eqToIso (pushforward_obj_eq_pushforward_restrictScalars i U hsub _)))
    (fun p q V a b => by
      have hE (n : ℤ) (x) :
          ((grZPieceIsoPushforwardConormal i U hsub hcl n).trans
            (eqToIso (pushforward_obj_eq_pushforward_restrictScalars i U hsub
              ((conormalAlgebra i).algebra.piece n)))).hom.val.app V x =
            (grZPieceIsoPushforwardConormal i U hsub hcl n).hom.val.app V x := by
        change (eqToHom (pushforward_obj_eq_pushforward_restrictScalars i U hsub
          ((conormalAlgebra i).algebra.piece n))).val.app V
            ((grZPieceIsoPushforwardConormal i U hsub hcl n).hom.val.app V x) = _
        generalize (grZPieceIsoPushforwardConormal i U hsub hcl n).hom.val.app V x = z
        have key : ∀ {M N : (U : Scheme.{u}).Modules} (h : M = N) (z : M.val.obj V),
            HEq ((eqToHom h).val.app V z) z := fun h _ => by subst h; rfl
        exact eq_of_heq (key _ z)
      exact (hE (p + q) _).trans ((grZPieceIsoPushforwardConormal_mul i U hsub hcl p q V.unop
        a b).trans (congrArg₂
          (fun (s : ((conormalAlgebra i).algebra.piece p).val.obj
              (op (openLift i U hsub ⁻¹ᵁ V.unop)))
            (t : ((conormalAlgebra i).algebra.piece q).val.obj
              (op (openLift i U hsub ⁻¹ᵁ V.unop))) =>
            ((conormalAlgebra i).algebra.mul p q).app (op (openLift i U hsub ⁻¹ᵁ V.unop)) s t)
          (hE p a).symm (hE q b).symm)))

/-- The degree-`n` component of `Stacks.Conormal.inverseImageGrIsoConormal` is the degreewise
identification `Stacks.Conormal.inverseImageGrPieceIsoConormal`. -/
theorem inverseImageGrIsoConormal_hom_app (n : ℤ) :
    (inverseImageGrIsoConormal i U hsub hcl).hom.app n =
      (inverseImageGrPieceIsoConormal i U hsub hcl n).hom :=
  rfl

/-- The identification of `i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` with the conormal algebra carries the graded
unit to the graded unit over every open. -/
theorem inverseImageGrIsoConormal_one (W : Z.Opens) :
    ((inverseImageGrIsoConormal i U hsub hcl).hom.app 0).val.app (op W)
        ((inverseImageGradedAlgebra (openLift i U hsub).base (U.toScheme).sheaf
          (grGradedAlgebra (openIdeal i U hsub))).one.eval (op W)) =
      (conormalAlgebra i).algebra.one.eval (op W) :=
  SheafOfModules.GradedAlgebra.iso_hom_app_one_eval (inverseImageGrIsoConormal i U hsub hcl) (op W)

/-- Let `i : Z ⟶ X` be an immersion and `U ⊆ X` an open
subscheme such that `i(Z) ⊆ U` is a closed subset of `U`; let `ℐ ⊆ 𝒪_U` be the quasi-coherent
ideal sheaf of the closed subscheme `i(Z) ⊂ U`.  Then
`𝒞_{Z/X,*} = i^*(⨁_{n ≥ 0} ℐⁿ) = i^{-1}(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`:
* the conormal algebra is isomorphic to `i^*(⨁ₙ ℐⁿ)` as sheaves of graded `𝒪_Z`-algebras, the
  isomorphism carrying the unit to the unit;
* the topological inverse image `i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`, a sheaf of graded `i^{-1}𝒪_U`-algebras,
  is isomorphic to the conormal algebra read over `i^{-1}𝒪_U` along the structure map
  `i^{-1}𝒪_U ⟶ 𝒪_Z`, as sheaves of graded algebras, the isomorphism carrying the unit to the
  unit.

The isomorphisms are `Stacks.Conormal.conormalIsoReesPullback` and
`Stacks.Conormal.inverseImageGrIsoConormal`. -/
@[stacks 0633 "part (1)"]
theorem conormalAlgebra_identifications :
    (∃ e : (conormalAlgebra i).algebra ≅ openReesPullback i U hsub, ∀ W : Z.Opens,
      (e.hom.app 0).val.app (op W) ((conormalAlgebra i).algebra.one.eval (op W)) =
        (openReesPullback i U hsub).one.eval (op W)) ∧
    (∃ e : inverseImageGradedAlgebra (openLift i U hsub).base (U.toScheme).sheaf
          (grGradedAlgebra (openIdeal i U hsub)) ≅
        SheafOfModules.GradedAlgebra.scalarRestrict (openStructureMap i U hsub)
          (conormalAlgebra i).algebra, ∀ W : Z.Opens,
      (e.hom.app 0).val.app (op W)
          ((inverseImageGradedAlgebra (openLift i U hsub).base (U.toScheme).sheaf
            (grGradedAlgebra (openIdeal i U hsub))).one.eval (op W)) =
        (conormalAlgebra i).algebra.one.eval (op W)) :=
  ⟨⟨conormalIsoReesPullback i U hsub hcl, conormalIsoReesPullback_one i U hsub hcl⟩,
    ⟨inverseImageGrIsoConormal i U hsub hcl, inverseImageGrIsoConormal_one i U hsub hcl⟩⟩

end Presentation

end Stacks.Conormal

end
