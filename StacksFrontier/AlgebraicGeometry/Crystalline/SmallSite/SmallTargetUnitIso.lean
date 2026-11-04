module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmallTargetDomination
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanPointwiseMap

/-!
# `f_{CRIS, *}` of the unit of `π_{X, *} ⊣ i_{X, *}` is invertible on the small site

Let `f : X ⟶ X'` be a morphism of the global crystalline situations of [Stacks, Tag 07I5].  For an
abelian sheaf `ℱ` on the big crystalline site `CRIS(X/S)` the unit

`η_ℱ : ℱ ⟶ i_{X, *}π_{X, *}ℱ`

of the adjunction `π_{X, *} ⊣ i_{X, *}` of [Stacks, Tag 07IJ] becomes invertible after
`π_{X', *} ∘ f_{CRIS, *}`, that is on the small crystalline site of the target:
`Crystalline.GlobalCrystallineSituation.SmallSite.isIso_smallRestriction_changeBase_unit`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `changeBaseRanCone` and `isLimitChangeBaseRanCone` — the limit cone computing the sections of
  `f_{CRIS, *}` at an object of the small site of the target, and that it is a limit cone.
* `dominationPiOf` — the projection of the limit computing `(f_{CRIS, *}i_{X, *}π_{X, *}ℱ)(D)`,
  for `D` an object of `Cris(X'/S')`, attached to a factorization of a morphism `f_CRIS(A) ⟶ D`
  through an object of `Cris(X/S)`.
* `dominationUnitPi` — the same at a chosen factorization.
* `dominationUnitLeg` — the amalgamation of those projections over the covering sieve of the
  factorizations: one leg of the inverse cone.
* `dominationUnitCone` and `dominationUnitInv` — the inverse cone and, out of it, **the inverse**
  of the comparison at `D`.

## Main results

* `dominationPiOf_eq` — **the projections do not depend on the factorization.**
* `isIso_changeBaseRanUnit` — the comparison is invertible at every object of the small site
  of the target.
* `isIso_smallRestriction_changeBase_unit` — **`π_{X', *}f_{CRIS, *}(η_ℱ)` is invertible.**

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

open CrystallineThickening

namespace SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-! ### The limit cone computing `f_{CRIS, *}` at an object of the small site -/

section Cone

variable (W : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (D : CrystallineThickening S')

/-- **The limit cone computing the sections of `f_{CRIS, *}ℋ` at an object `D` of
`Cris(X'/S')`**: the limit of `ℋ(A)` over the objects `A` of `CRIS(X/S)` with a morphism
`f_CRIS(A) ⟶ D`, the cone of the right Kan extension counit. -/
abbrev changeBaseRanCone :
    Cone (StructuredArrow.proj (op ((ι S').obj D)) (changeBase S S' fS fX hf).op ⋙ W) :=
  (Functor.RightExtension.mk _
    ((changeBase S S' fS fX hf).op.ranCounit.app W)).coneAt (op ((ι S').obj D))

/-- **The cone `changeBaseRanCone` is a limit cone.** -/
def isLimitChangeBaseRanCone : IsLimit (changeBaseRanCone S S' fS fX hf W D) :=
  (changeBase S S' fS fX hf).op.isPointwiseRightKanExtensionRanCounit W (op ((ι S').obj D))

/-- **The index of the limit cone attached to a morphism `f_CRIS(A) ⟶ D`.** -/
abbrev ranIndex (A : Thickening S) (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) :
    StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op :=
  StructuredArrow.mk (Y := op A) ψ.op

/-- The structure morphism of the index attached to `ψ` is `ψ`. -/
@[simp]
theorem ranIndex_hom_unop (A : Thickening S)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) :
    (ranIndex S S' fS fX hf D A ψ).hom.unop = ψ :=
  rfl

/-- The object of `CRIS(X/S)` of the index attached to `ψ` is the source of `ψ`. -/
@[simp]
theorem ranIndex_right (A : Thickening S)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) :
    (ranIndex S S' fS fX hf D A ψ).right = op A :=
  rfl

/-- **Reading a projection of the limit cone along a morphism of `CRIS(X/S)`** gives the
projection at the composite index. -/
theorem changeBaseRanCone_π_comp
    (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op)
    (A₀ : Thickening S) (g : A₀ ⟶ d.right.unop) :
    (changeBaseRanCone S S' fS fX hf W D).π.app d ≫ W.map g.op =
      (changeBaseRanCone S S' fS fX hf W D).π.app
        (ranIndex S S' fS fX hf D A₀ ((changeBase S S' fS fX hf).map g ≫ d.hom.unop)) :=
  (changeBaseRanCone S S' fS fX hf W D).w
    (show d ⟶ ranIndex S S' fS fX hf D A₀
        ((changeBase S S' fS fX hf).map g ≫ d.hom.unop) from
      StructuredArrow.homMk g.op rfl)

end Cone

/-! ### The projections attached to a factorization through the small site -/

section Pi

variable (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (D : CrystallineThickening S')

/-- **The presheaf underlying `i_{X, *}π_{X, *}ℱ`**, the right Kan extension along the inclusion
of the small crystalline site of the restriction of `ℱ` to it. -/
abbrev unitTargetPresheaf (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (ι S).op.ran.obj ((ι S).op ⋙ G.obj)

/-- **The projection of the limit computing `(f_{CRIS, *}i_{X, *}π_{X, *}ℱ)(D)` attached to a
factorization of a morphism to `D` through an object of `Cris(X/S)`**: the projection of the limit
cone at `(i_X B, h)`, followed by the Kan extension counit at `B` — which identifies the sections
of `i_{X, *}π_{X, *}ℱ` over `i_X B` with those of `ℱ` — followed by restriction along `m`. -/
def dominationPiOf (A : Thickening S) (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D) :
    (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt ⟶ G.obj.obj (op A) :=
  (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).π.app
      (ranIndex S S' fS fX hf D ((ι S).obj B) h) ≫
    ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app (op B) ≫ G.obj.map m.op

/-- **Restricting `dominationPiOf` along a morphism of `CRIS(X/S)`** composes it into the
factorization. -/
theorem dominationPiOf_comp_map (A A₀ : Thickening S) (g : A₀ ⟶ A)
    (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D) :
    dominationPiOf S S' fS fX hf G D A B m h ≫ G.obj.map g.op =
      dominationPiOf S S' fS fX hf G D A₀ B (g ≫ m) h := by
  have h₁ : G.obj.map m.op ≫ G.obj.map g.op = G.obj.map (g ≫ m).op := by
    rw [← G.obj.map_comp, ← op_comp]
  rw [dominationPiOf, dominationPiOf, Category.assoc, Category.assoc, h₁]

/-- **Replacing the dominating object of a factorization by one refining it** leaves
`dominationPiOf` unchanged. -/
theorem dominationPiOf_comp_hom (A : Thickening S) (B B₀ : CrystallineThickening S)
    (a : B₀ ⟶ B) (m : A ⟶ (ι S).obj B₀)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D) :
    dominationPiOf S S' fS fX hf G D A B (m ≫ (ι S).map a) h =
      dominationPiOf S S' fS fX hf G D A B₀ m
        ((changeBase S S' fS fX hf).map ((ι S).map a) ≫ h) := by
  have hcounit : ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app (op B) ≫
        G.obj.map ((ι S).map a).op =
      (unitTargetPresheaf S G).map ((ι S).map a).op ≫
        ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app (op B₀) :=
    (((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).naturality a.op).symm
  rw [dominationPiOf, dominationPiOf, op_comp, G.obj.map_comp, ← Category.assoc,
    ← Category.assoc, Category.assoc
      (((changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).π.app
        (ranIndex S S' fS fX hf D ((ι S).obj B) h))), hcounit, ← Category.assoc,
    changeBaseRanCone_π_comp S S' fS fX hf (unitTargetPresheaf S G) D
      (ranIndex S S' fS fX hf D ((ι S).obj B) h) ((ι S).obj B₀) ((ι S).map a), Category.assoc,
    ranIndex_hom_unop]

/-- **The projection does not depend on the factorization.**  Two factorizations of the same
morphism `ψ : f_CRIS(A) ⟶ D` through objects of `Cris(X/S)` give the same projection. -/
theorem dominationPiOf_eq (A : Thickening S)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D)
    (B₁ : CrystallineThickening S) (m₁ : A ⟶ (ι S).obj B₁)
    (h₁ : (changeBase S S' fS fX hf).obj ((ι S).obj B₁) ⟶ (ι S').obj D)
    (hmh₁ : (changeBase S S' fS fX hf).map m₁ ≫ h₁ = ψ)
    (B₂ : CrystallineThickening S) (m₂ : A ⟶ (ι S).obj B₂)
    (h₂ : (changeBase S S' fS fX hf).obj ((ι S).obj B₂) ⟶ (ι S').obj D)
    (hmh₂ : (changeBase S S' fS fX hf).map m₂ ≫ h₂ = ψ) :
    dominationPiOf S S' fS fX hf G D A B₁ m₁ h₁ = dominationPiOf S S' fS fX hf G D A B₂ m₂ h₂ := by
  refine G.property.hom_ext ⟨commonRefinementSieve S S' fS fX hf D A B₁ B₂ m₁ h₁ m₂ h₂,
    commonRefinementSieve_mem S S' fS fX hf D A ψ B₁ B₂ m₁ h₁ hmh₁ m₂ h₂ hmh₂⟩ _ _ fun I ↦ ?_
  obtain ⟨B, m, a₁, a₂, e₁, e₂, e₃⟩ := I.hf
  rw [dominationPiOf_comp_map, dominationPiOf_comp_map, ← e₁, ← e₂, dominationPiOf_comp_hom,
    dominationPiOf_comp_hom, e₃]

end Pi

/-! ### The inverse of the comparison -/

section Inverse

variable (D : CrystallineThickening S')

/-- **The object of `Cris(X/S)` of a chosen factorization.** -/
def dominationObj (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ) : CrystallineThickening S :=
  hdom.choose

/-- **The morphism to the object of a chosen factorization.** -/
def dominationHom (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ) :
    A ⟶ (ι S).obj (dominationObj S S' fS fX hf D A hdom) :=
  hdom.choose_spec.choose

/-- **The morphism down to `D` of a chosen factorization.** -/
def dominationTarget (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ) :
    (changeBase S S' fS fX hf).obj ((ι S).obj (dominationObj S S' fS fX hf D A hdom)) ⟶
      (ι S').obj D :=
  hdom.choose_spec.choose_spec.choose

/-- The chosen factorization is a factorization. -/
theorem dominationFac (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ) :
    (changeBase S S' fS fX hf).map (dominationHom S S' fS fX hf D A hdom) ≫
      dominationTarget S S' fS fX hf D A hdom = ψ :=
  hdom.choose_spec.choose_spec.choose_spec

/-- **The projection attached to a chosen factorization.** -/
def dominationUnitPi (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ) :
    (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt ⟶ G.obj.obj (op A) :=
  dominationPiOf S S' fS fX hf G D A (dominationObj S S' fS fX hf D A hdom)
    (dominationHom S S' fS fX hf D A hdom) (dominationTarget S S' fS fX hf D A hdom)

/-- **`dominationUnitPi` is `dominationPiOf` at every factorization.** -/
theorem dominationUnitPi_eq (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (A : Thickening S)
    {ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D}
    (hdom : IsDominatedOver S S' fS fX hf D A ψ)
    (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D)
    (hmh : (changeBase S S' fS fX hf).map m ≫ h = ψ) :
    dominationUnitPi S S' fS fX hf D G A hdom = dominationPiOf S S' fS fX hf G D A B m h :=
  dominationPiOf_eq S S' fS fX hf G D A ψ _ _ _ (dominationFac S S' fS fX hf D A hdom) B m h hmh

/-- **The covering of an index of the limit by the refinements over which the structure morphism
factors through the small site.** -/
def dominationUnitCover (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op) :
    (topology S).Cover d.right.unop :=
  ⟨dominationOverSieve S S' fS fX hf D d.right.unop d.hom.unop,
    dominationOverSieve_mem S S' fS fX hf D d.right.unop d.hom.unop⟩

/-- **One leg of the inverse cone**: the amalgamation over `dominationUnitCover` of the
projections `dominationUnitPi`. -/
def dominationUnitLeg (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op) :
    (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt ⟶ G.obj.obj d.right :=
  G.property.amalgamate (dominationUnitCover S S' fS fX hf D d)
    (fun I ↦ dominationUnitPi S S' fS fX hf D G I.Y I.hf)
    (fun {I₁ I₂} r ↦ by
      rw [dominationUnitPi_eq S S' fS fX hf D G I₁.Y I₁.hf _ _ _
          (dominationFac S S' fS fX hf D I₁.Y I₁.hf),
        dominationUnitPi_eq S S' fS fX hf D G I₂.Y I₂.hf _ _ _
          (dominationFac S S' fS fX hf D I₂.Y I₂.hf),
        dominationPiOf_comp_map, dominationPiOf_comp_map]
      refine dominationPiOf_eq S S' fS fX hf G D r.Z
        ((changeBase S S' fS fX hf).map (r.g₁ ≫ I₁.f) ≫ d.hom.unop) _ _ _ ?_ _ _ _ ?_
      · rw [Functor.map_comp, Category.assoc, dominationFac S S' fS fX hf D I₁.Y I₁.hf,
          ← Category.assoc, ← Functor.map_comp]
      · rw [Functor.map_comp, Category.assoc, dominationFac S S' fS fX hf D I₂.Y I₂.hf,
          ← Category.assoc, ← Functor.map_comp, r.w])

/-- Restricting the leg `dominationUnitLeg` along an arrow of the covering sieve is the projection
`dominationUnitPi` at the source of that arrow. -/
theorem dominationUnitLeg_comp_map (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op)
    (I : (dominationUnitCover S S' fS fX hf D d).Arrow) :
    dominationUnitLeg S S' fS fX hf D G d ≫ G.obj.map I.f.op =
      dominationUnitPi S S' fS fX hf D G I.Y I.hf :=
  G.property.amalgamate_map _ _ _ I

/-- **The unit of `π_{X, *} ⊣ i_{X, *}` on underlying presheaves**, the unit of the right Kan
extension adjunction along the inclusion of the small crystalline site. -/
abbrev unitPresheafMap (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    G.obj ⟶ unitTargetPresheaf S G :=
  ((ι S).op.ranAdjunction AddCommGrpCat.{u + 1}).unit.app G.obj

omit hf in
/-- **The unit followed by a projection of the limit computing `i_{X, *}π_{X, *}ℱ` is restriction
along that projection's own structure morphism.** -/
theorem unitPresheafMap_comp_coneAt_π (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (Z : (Thickening S)ᵒᵖ) (e : StructuredArrow Z (ι S).op) :
    (unitPresheafMap S G).app Z ≫
        ((Functor.RightExtension.mk (unitTargetPresheaf S G)
          ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj))).coneAt Z).π.app e =
      G.obj.map e.hom := by
  show (unitPresheafMap S G).app Z ≫
      (unitTargetPresheaf S G).map e.hom ≫
        ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app e.right = G.obj.map e.hom
  rw [← Category.assoc, ← (unitPresheafMap S G).naturality e.hom, Category.assoc,
    (ι S).op.ranCounit_app_app_ranAdjunction_unit_app_app G.obj e.right]
  exact Category.comp_id _

/-- **The comparison map at `D`**: `f_{CRIS, *}` of the unit, read at an object of the small site
of the target. -/
abbrev changeBaseRanUnit (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    (changeBaseRanCone S S' fS fX hf G.obj D).pt ⟶
      (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt :=
  ((changeBase S S' fS fX hf).op.ran.map (unitPresheafMap S G)).app (op ((ι S').obj D))

/-- **The inverse cone**: the amalgamations `dominationUnitLeg` form a cone on the diagram whose
limit is the sections of `f_{CRIS, *}ℱ` at `D`. -/
def dominationUnitCone (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    Cone (StructuredArrow.proj (op ((ι S').obj D)) (changeBase S S' fS fX hf).op ⋙ G.obj) where
  pt := (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt
  π :=
    { app := dominationUnitLeg S S' fS fX hf D G
      naturality := fun d d' φ ↦ by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
          StructuredArrow.proj_map]
        rw [Category.id_comp]
        refine (G.property.hom_ext (dominationUnitCover S S' fS fX hf D d') _ _ fun I ↦ ?_).symm
        have hI := I.hf
        obtain ⟨B, m, h, hmh⟩ := hI
        have hφ : (changeBase S S' fS fX hf).map φ.right.unop ≫ d.hom.unop = d'.hom.unop :=
          congrArg Quiver.Hom.unop (StructuredArrow.w φ)
        have hd' : (changeBase S S' fS fX hf).map (I.f ≫ φ.right.unop) ≫ d.hom.unop =
            (changeBase S S' fS fX hf).map I.f ≫ d'.hom.unop := by
          rw [Functor.map_comp, Category.assoc, hφ]
        have hZ : IsDominatedOver S S' fS fX hf D I.Y
            ((changeBase S S' fS fX hf).map (I.f ≫ φ.right.unop) ≫ d.hom.unop) :=
          ⟨B, m, h, hmh.trans hd'.symm⟩
        rw [Category.assoc, ← G.obj.map_comp,
          show φ.right ≫ I.f.op = (I.f ≫ φ.right.unop).op from rfl,
          dominationUnitLeg_comp_map S S' fS fX hf D G d ⟨I.Y, I.f ≫ φ.right.unop, hZ⟩,
          dominationUnitLeg_comp_map S S' fS fX hf D G d' I,
          dominationUnitPi_eq S S' fS fX hf D G I.Y hZ B m h (hmh.trans hd'.symm),
          dominationUnitPi_eq S S' fS fX hf D G I.Y I.hf B m h hmh] }

/-- **The inverse of the comparison map at `D`**, the morphism out of the limit over the
factorizations induced by the cone `dominationUnitCone`. -/
def dominationUnitInv (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).pt ⟶
      (changeBaseRanCone S S' fS fX hf G.obj D).pt :=
  (isLimitChangeBaseRanCone S S' fS fX hf G.obj D).lift
    (dominationUnitCone S S' fS fX hf D G)

/-- Reading the inverse at an index of the limit gives back the leg it was built from. -/
theorem dominationUnitInv_comp_π (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op) :
    dominationUnitInv S S' fS fX hf D G ≫
        (changeBaseRanCone S S' fS fX hf G.obj D).π.app d =
      dominationUnitLeg S S' fS fX hf D G d :=
  (isLimitChangeBaseRanCone S S' fS fX hf G.obj D).fac
    (dominationUnitCone S S' fS fX hf D G) d

/-- **The projection of the limit over the factorizations at a factorization, read against the
comparison map**: the comparison followed by `dominationPiOf` is the projection of the limit of
`ℱ` at the index the factorization produces. -/
theorem changeBaseRanUnit_comp_dominationPiOf (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (A : Thickening S) (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D) :
    changeBaseRanUnit S S' fS fX hf D G ≫ dominationPiOf S S' fS fX hf G D A B m h =
      (changeBaseRanCone S S' fS fX hf G.obj D).π.app
        (ranIndex S S' fS fX hf D A ((changeBase S S' fS fX hf).map m ≫ h)) := by
  have htri : (unitPresheafMap S G).app (op ((ι S).obj B)) ≫
      ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app (op B) = 𝟙 _ :=
    (ι S).op.ranCounit_app_app_ranAdjunction_unit_app_app G.obj (op B)
  rw [dominationPiOf, ← Category.assoc,
    Functor.ran_map_app_comp_coneAt_π (changeBase S S' fS fX hf).op (unitPresheafMap S G)
      (op ((ι S').obj D)) (ranIndex S S' fS fX hf D ((ι S).obj B) h)]
  dsimp only [ranIndex_right]
  rw [Category.assoc, ← Category.assoc ((unitPresheafMap S G).app (op ((ι S).obj B))), htri,
    Category.id_comp,
    changeBaseRanCone_π_comp S S' fS fX hf G.obj D
      (ranIndex S S' fS fX hf D ((ι S).obj B) h) A m, ranIndex_hom_unop]

/-- **A projection of the limit computing `(f_{CRIS, *}i_{X, *}π_{X, *}ℱ)(D)`, followed by a
projection of the limit computing `i_{X, *}π_{X, *}ℱ` at that index**, is the projection
`dominationPiOf` attached to the tautological factorization of an object of `Cris(X/S)` through
itself. -/
theorem changeBaseRanCone_π_comp_unitConeAt (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (d : StructuredArrow (op ((ι S').obj D)) (changeBase S S' fS fX hf).op)
    (e : StructuredArrow d.right (ι S).op) :
    (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).π.app d ≫
        ((Functor.RightExtension.mk (unitTargetPresheaf S G)
          ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj))).coneAt d.right).π.app e =
      dominationPiOf S S' fS fX hf G D ((ι S).obj (unop e.right)) (unop e.right) (𝟙 _)
        ((changeBase S S' fS fX hf).map e.hom.unop ≫ d.hom.unop) := by
  show (changeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).π.app d ≫
      (unitTargetPresheaf S G).map e.hom.unop.op ≫
        ((ι S).op.ranCounit.app ((ι S).op ⋙ G.obj)).app (op (unop e.right)) = _
  rw [dominationPiOf, op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Category.assoc,
    changeBaseRanCone_π_comp S S' fS fX hf (unitTargetPresheaf S G) D d
      ((ι S).obj (unop e.right)) e.hom.unop]

/-- **The comparison map at `D` is invertible**, `dominationUnitInv` being its inverse. -/
instance isIso_changeBaseRanUnit (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    IsIso (changeBaseRanUnit S S' fS fX hf D G) := by
  refine ⟨dominationUnitInv S S' fS fX hf D G, ?_, ?_⟩
  · refine (isLimitChangeBaseRanCone S S' fS fX hf G.obj D).hom_ext fun d ↦ ?_
    rw [Category.assoc, dominationUnitInv_comp_π, Category.id_comp]
    refine G.property.hom_ext (dominationUnitCover S S' fS fX hf D d) _ _ fun I ↦ ?_
    have hI := I.hf
    obtain ⟨B, m, h, hmh⟩ := hI
    rw [Category.assoc, dominationUnitLeg_comp_map S S' fS fX hf D G d I,
      dominationUnitPi_eq S S' fS fX hf D G I.Y I.hf B m h hmh,
      changeBaseRanUnit_comp_dominationPiOf, hmh,
      changeBaseRanCone_π_comp S S' fS fX hf G.obj D d I.Y I.f]
  · refine (isLimitChangeBaseRanCone S S' fS fX hf (unitTargetPresheaf S G) D).hom_ext fun d ↦ ?_
    rw [Category.assoc,
      Functor.ran_map_app_comp_coneAt_π (changeBase S S' fS fX hf).op (unitPresheafMap S G)
        (op ((ι S').obj D)) d,
      ← Category.assoc, dominationUnitInv_comp_π, Category.id_comp]
    refine ((ι S).op.isPointwiseRightKanExtensionRanCounit ((ι S).op ⋙ G.obj)
      d.right).hom_ext fun e ↦ ?_
    have hid : (changeBase S S' fS fX hf).map (𝟙 ((ι S).obj (unop e.right))) ≫
        ((changeBase S S' fS fX hf).map e.hom.unop ≫ d.hom.unop) =
          (changeBase S S' fS fX hf).map e.hom.unop ≫ d.hom.unop := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    have hdom : IsDominatedOver S S' fS fX hf D ((ι S).obj (unop e.right))
        ((changeBase S S' fS fX hf).map e.hom.unop ≫ d.hom.unop) :=
      ⟨unop e.right, 𝟙 _, _, hid⟩
    have hleg : dominationUnitLeg S S' fS fX hf D G d ≫ G.obj.map e.hom =
        dominationUnitPi S S' fS fX hf D G ((ι S).obj (unop e.right)) hdom :=
      dominationUnitLeg_comp_map S S' fS fX hf D G d
        ⟨(ι S).obj (unop e.right), e.hom.unop, hdom⟩
    rw [Category.assoc, unitPresheafMap_comp_coneAt_π,
      changeBaseRanCone_π_comp_unitConeAt S S' fS fX hf D G d e, hleg,
      dominationUnitPi_eq S S' fS fX hf D G ((ι S).obj (unop e.right)) hdom (unop e.right) (𝟙 _) _
        hid]

end Inverse

/-! ### The statement on sheaves -/

section SheafLevel

/-- **`π_{X', *}f_{CRIS, *}` of the unit of `π_{X, *} ⊣ i_{X, *}` is invertible.**  For every
abelian sheaf `ℱ` on the big crystalline site `CRIS(X/S)` the comparison

`π_{X', *}f_{CRIS, *}ℱ ⟶ π_{X', *}f_{CRIS, *}i_{X, *}π_{X, *}ℱ`

is an isomorphism of abelian sheaves on the small crystalline site `Cris(X'/S')`. -/
instance isIso_smallRestriction_changeBase_unit
    (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    IsIso ((smallRestriction S').map ((changeBaseDirectImage S S' fS fX hf).map
      ((bigDirectImageAdjunction S).unit.app G))) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf (smallTopology S') AddCommGrpCat.{u + 1}),
    NatTrans.isIso_iff_isIso_app]
  intro X
  have hu : ((bigDirectImageAdjunction S).unit.app G).hom = unitPresheafMap S G :=
    (CrystallineThickening.ι S).sheafAdjunctionCocontinuous_unit_app_hom
      AddCommGrpCat.{u + 1} (smallTopology S) (topology S) G
  have heq : ((sheafToPresheaf (smallTopology S') AddCommGrpCat.{u + 1}).map
        ((smallRestriction S').map ((changeBaseDirectImage S S' fS fX hf).map
          ((bigDirectImageAdjunction S).unit.app G)))).app X =
      changeBaseRanUnit S S' fS fX hf (unop X) G := by
    change ((changeBase S S' fS fX hf).op.ran.map
      ((bigDirectImageAdjunction S).unit.app G).hom).app (op ((ι S').obj (unop X))) = _
    rw [hu]
    rfl
  rw [heq]
  exact isIso_changeBaseRanUnit S S' fS fX hf (unop X) G

end SheafLevel

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
