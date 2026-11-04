module

public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.PowerEpi
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Symmetric powers of a free sheaf of modules

Tag 00DN says that every symmetric power of a free module over a ring is free. This file proves
the corresponding statement for sheaves of modules on an arbitrary ringed site: the degree-`n`
homogeneous piece of the symmetric algebra of `SheafOfModules.free I` is
`SheafOfModules.free` on the degree-`n` monomials in `I`
(`Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso`). It is the free half of clause (6) of
Tag 01CK, and it is what the free terms of the presentation sequences of Tag 01CJ need in order
to give clauses (3) and (5) of Tag 01CK.

There is no stalk and no local computation anywhere: the degree-`n` piece of the symmetric
algebra of a sheaf of modules is by construction the sheafification of the *sectionwise*
symmetric powers of its underlying presheaf (`Stacks.GradedAlgebra.sheafify_piece`), the
sectionwise statement is the naturality of the monomial basis proved in
`StacksDraft.AlgebraicGeometry.F3b.SymmetricFree.Basic`, and the two ends are tied together by
`SheafOfModules.symmetricPieceSheafifyIso`.

## Main definitions

* `Stacks.SymmetricFree.freeObjCofan` and `isColimitFreeObjCofan`: **the free presheaf of modules
  on a constant presheaf of types `I` is the coproduct of `I` copies of the structure
  presheaf.** Mathlib has `PresheafOfModules.freeObj` and `SheafOfModules.free` and nothing
  comparing them; this is the presheaf-level half of that comparison.
* `Stacks.SymmetricFree.sheafifyFreeObjIso`: **the sheafification of the free presheaf of modules
  on the constant presheaf `I` is `SheafOfModules.free I`**, by sheafification preserving
  coproducts and the counit of the sheafification adjunction at `SheafOfModules.unit`.
* `Stacks.SymmetricFree.SectionwiseBasis.sheafifyIso`: a presheaf of modules with a
  restriction-compatible basis of its sections indexed by `I` sheafifies to
  `SheafOfModules.free I`.
* `Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso`: **Tag 00DN at the sheaf level.**

## Implementation notes

**No `@[stacks]` tag.** Tag 00DN is a statement about modules over a ring, and about the
exterior power as well as the symmetric one; it is already available for modules as
`SymPow.free_symmetricPower`. What is here is the sheaf-theoretic analogue of its symmetric
half, which is an *ingredient* of clause (6) of Tag 01CK rather than either tag: clause (6) is
about a *locally* free sheaf, and the exterior analogue — which needs the same naturality for
`ExteriorAlgebra`, not proved here — would also be required. A tag on this declaration would
report either tag as covered when it is not.

**The sheafification is taken along the identity of the ring presheaf**, which is what
`SheafOfModules.sheafifiedSymmetricAlgebra` does, and it is what makes the counit of the
sheafification adjunction have `PresheafOfModules.unit R.obj` for its source definitionally.
For a general `α : R₀ ⟶ R.obj` the right adjoint does not send `SheafOfModules.unit R` to
`PresheafOfModules.unit R₀`, so `Stacks.SymmetricFree.sheafifyUnitIso` would not typecheck.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite Module
  PresheafOfModules

universe v u w

namespace Stacks.SymmetricFree

section Free

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- The inclusion of the `i`-th copy of the structure presheaf into the free presheaf of
modules on the constant presheaf of types `I`. -/
noncomputable def freeObjι (I : Type w) (i : I) :
    PresheafOfModules.unit R ⟶ freeObj ((Functor.const Cᵒᵖ).obj I) where
  app _X := ModuleCat.ofHom (Finsupp.lsingle i)
  naturality {_X _Y} f :=
    ModuleCat.hom_ext (LinearMap.ext_ring
      (freeObj_const_restrictₛₗ_single I f i (1 : R.obj _)).symm)

/-- On sections over `X`, the inclusion `freeObjι I i` sends `r` to `Finsupp.single i r`. -/
theorem freeObjι_app (I : Type w) (i : I) (X : Cᵒᵖ) (r : R.obj X) :
    Hom.app (freeObjι (R := R) I i) X r = Finsupp.single i r := rfl

/-- The morphism `freeObjDesc φ` out of a free presheaf of modules sends the generator
`Finsupp.single i 1` over `X` to the section `φ.app X i`. -/
theorem freeObjDesc_single {F : Cᵒᵖ ⥤ Type w} {G : PresheafOfModules.{w} R}
    (φ : F ⟶ G.presheaf ⋙ forget _) (X : Cᵒᵖ) (i : F.obj X) :
    Hom.app (freeObjDesc φ) X (Finsupp.single i 1) = φ.app X i := by
  rw [freeObjDesc_app]
  exact ModuleCat.freeDesc_apply (φ.app X) i

/-- The free presheaf of modules on the constant presheaf of types `I`, as a cofan of copies of
the structure presheaf. -/
noncomputable def freeObjCofan (I : Type w) :
    Cofan (fun _ : I => PresheafOfModules.unit R) :=
  Cofan.mk (freeObj ((Functor.const Cᵒᵖ).obj I)) (freeObjι I)

/-- The family of sections of a cocone over the copies of the structure presheaf, read as a
morphism of presheaves of types out of the constant presheaf. -/
noncomputable def freeObjCofanDescApp {I : Type w}
    (t : Cofan (fun _ : I => PresheafOfModules.unit R)) :
    (Functor.const Cᵒᵖ).obj I ⟶ t.pt.presheaf ⋙ forget _ where
  app X := ↾fun i => Hom.app (t.inj i) X (1 : R.obj X)
  naturality {X Y} f := by
    ext i
    exact ((naturality_apply (t.inj i) f (1 : R.obj X)).symm.trans
      (congrArg (Hom.app (t.inj i) Y) (unit_map_one R f))).symm

/-- **The free presheaf of modules on the constant presheaf of types `I` is the coproduct of `I`
copies of the structure presheaf.** -/
noncomputable def isColimitFreeObjCofan (I : Type w) :
    IsColimit (freeObjCofan (R := R) I) :=
  Cofan.IsColimit.mk _ (fun t => freeObjDesc (freeObjCofanDescApp t))
    (fun t i => PresheafOfModules.hom_ext fun X =>
      ModuleCat.hom_ext (LinearMap.ext_ring (freeObjDesc_single (freeObjCofanDescApp t) X i)))
    (fun t _m hm => PresheafOfModules.hom_ext fun X =>
      ModuleCat.free_hom_ext fun i =>
        ((congrArg (fun φ : PresheafOfModules.unit R ⟶ t.pt => Hom.app φ X (1 : R.obj X))
          (hm i)).trans (freeObjDesc_single (freeObjCofanDescApp t) X i).symm))

end Free

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sheafification of the structure presheaf is the structure sheaf, read as a sheaf of
modules over itself: the counit of the sheafification adjunction at `SheafOfModules.unit`. -/
noncomputable def sheafifyUnitIso :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (PresheafOfModules.unit R.obj) ≅
      SheafOfModules.unit R :=
  @asIso _ _ _ _ ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app
      (SheafOfModules.unit R)) (NatIso.isIso_app_of_isIso _ _)

/-- **The sheafification of the free presheaf of modules on the constant presheaf of types `I` is
the free sheaf of modules on `I`.** -/
noncomputable def sheafifyFreeObjIso (I : Type w) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (freeObj ((Functor.const Cᵒᵖ).obj I)) ≅
      SheafOfModules.free (R := R) I :=
  letI : (PresheafOfModules.sheafification (𝟙 R.obj)).IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).isLeftAdjoint
  (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
      (isColimitFreeObjCofan I)).coconePointsIsoOfNatIso
    (SheafOfModules.isColimitFreeCofan I) (Discrete.natIso fun _ => sheafifyUnitIso)

/-- **A presheaf of modules with a basis of its sections indexed by `I`, compatible with
restriction, sheafifies to the free sheaf of modules on `I`.** -/
noncomputable def SectionwiseBasis.sheafifyIso {Q : PresheafOfModules.{w} R.obj} {I : Type w}
    (hQ : SectionwiseBasis Q I) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj Q ≅ SheafOfModules.free (R := R) I :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).mapIso hQ.isoFreeObj ≪≫ sheafifyFreeObjIso I

end Sheafify

section Symmetric

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tag 00DN at the sheaf level: the degree-`n` symmetric power of a free sheaf of modules is
free**, on the degree-`n` monomials in the index set. -/
noncomputable def sheafifiedSymmetricPieceFreeIso (I : Type w) (n : ℕ) :
    (SheafOfModules.sheafifiedSymmetricAlgebra J
        (SheafOfModules.free (R := toRingCat J Osharp) I)).piece (n : ℤ) ≅
      SheafOfModules.free (R := toRingCat J Osharp) {d : I →₀ ℕ | Finsupp.degree d = n} :=
  (SheafOfModules.symmetricPieceSheafifyIso J (freeObj ((Functor.const Cᵒᵖ).obj I))
      (SheafOfModules.free I) (sheafifyFreeObjIso I).symm (n : ℤ)).symm ≪≫
    ((freeObjSectionwiseBasis I).symPowInt n).sheafifyIso

end Symmetric

end Stacks.SymmetricFree

end
