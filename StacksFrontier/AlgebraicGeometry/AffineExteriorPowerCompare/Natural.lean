module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Wedge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial

/-!
# Naturality of the affine exterior-power comparison

**This file proves that `Stacks.AffineExteriorPower.tildeExteriorPowerIso` is natural in the
module**: it commutes with the associated sheaf of `⋀ⁿ(f)` on one side and with any unital
homomorphism of the exterior algebra sheaves extending `f` on the degree-one generators on the
other. This is the naturality assertion of Tag 01I8 for exterior powers.

## Main results

* `Stacks.AffineExteriorPower.tildeExteriorPowerIso_natural`: the naturality square, against an
  arbitrary unital homomorphism of exterior algebra sheaves extending `M̃ ⟶ Ñ`.
* `Stacks.AffineExteriorPower.tildeExteriorPowerIso_natural_exteriorPowerMap`: the same square for
  the canonical map `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap`, which the
  universal property of the exterior algebra produces.
* `Stacks.AffineExteriorPower.exteriorPowerΓIso_natural` and
  `Stacks.AffineExteriorPower.exteriorPowerΓIso_natural_exteriorPowerMap`: the two squares read on
  global sections.

## Implementation notes

The global-sections form is stated in the orientation in which the global-sections comparison
appears as `(exteriorPowerΓIso _ _ n).hom`, that is
`Γ(g) ≫ (exteriorPowerΓIso N B n).hom = (exteriorPowerΓIso M A n).hom ≫ ⋀ⁿ(f)`, reading
`Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M` as a natural isomorphism of functors in the module.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AffineExteriorPower

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N)

/-! ### Global sections determine a morphism out of an associated sheaf -/

/-- The canonical sections of an associated sheaf are natural in the module: the associated sheaf
of `h : X ⟶ Y` carries the section of `X̃` attached to `x` to the section of `Ỹ` attached to
`h x`. -/
theorem tilde_map_app_toOpen {X Y : ModuleCat.{u} R} (h : X ⟶ Y) (U : (Spec R).Opens) (x : X) :
    ((tilde.map h).val.app (op U)).hom ((tilde.toOpen X U).hom x) =
      (tilde.toOpen Y U).hom (h.hom x) :=
  congrArg (fun k => (ModuleCat.Hom.hom k) x) (tilde.toOpen_map_app h U)

/-- **The affine exterior-power comparison on a wedge of global sections**, written directly on
the sections of the sheaf rather than through the transpose of the affine adjunction. -/
theorem tildeExteriorPowerIso_hom_app_ιMulti (P : ModuleCat.{u} R) (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde P)) (s : Fin n → ↥P) :
    (tildeExteriorPowerIso P A n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥P)) ⊤).hom (exteriorPower.ιMulti ↥R n s)) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => A.exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen P ⊤).hom (s i))) :=
  tildeExteriorPowerIso_hom_ιMulti P n A s

/-- **Two morphisms out of `(⋀ⁿ_R M)~` agreeing on the canonical global sections attached to
wedges are equal.** -/
theorem hom_ext_ιMulti {n : ℕ} {F : (Spec R).Modules}
    {h₁ h₂ : (tilde (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) :
        SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ F}
    (H : ∀ s : Fin n → ↥M,
      h₁.val.app (specGlobalOpen R)
          ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom
            (exteriorPower.ιMulti ↥R n s)) =
        h₂.val.app (specGlobalOpen R)
          ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom
            (exteriorPower.ιMulti ↥R n s))) :
    h₁ = h₂ :=
  ((tilde.adjunction (R := R)).homEquiv (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) F).injective
    (ModuleCat.hom_ext
      (LinearMap.ext_on_range (exteriorPower.ιMulti_span ↥R n ↥M) fun s =>
        (tildeHomEquiv_apply (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) F h₁ _).trans
          ((H s).trans
            (tildeHomEquiv_apply (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) F h₂ _).symm)))

/-! ### The two composites on a wedge -/

/-- **The left composite of the naturality square on a wedge of global sections.** The associated
sheaf of `⋀ⁿ(f)` carries the section attached to `m₁ ∧ ⋯ ∧ mₙ` to the one attached to
`f m₁ ∧ ⋯ ∧ f mₙ`, and the comparison at `N` turns that into the ordered product of the
degree-one generators at the global sections of `Ñ` attached to the `f mᵢ`. -/
theorem tildeExteriorPowerIso_natural_left (n : ℕ)
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) (s : Fin n → ↥M) :
    (tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
          (exteriorPower.map n f.hom)) ≫ (tildeExteriorPowerIso N B n).hom).val.app
        (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom (exteriorPower.ιMulti ↥R n s)) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => B.exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen N ⊤).hom (f.hom (s i)))) := by
  show (tildeExteriorPowerIso N B n).hom.val.app (specGlobalOpen R)
      ((tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
          (exteriorPower.map n f.hom))).val.app (specGlobalOpen R) _) = _
  rw [tilde_map_app_toOpen]
  refine Eq.trans (congrArg (fun x : ↥(⋀[↥R]^n ↥N) =>
      (tildeExteriorPowerIso N B n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N)) ⊤).hom x))
    (exteriorPower.map_apply_ιMulti (R := ↥R) (n := n) f.hom s)) ?_
  exact tildeExteriorPowerIso_hom_app_ιMulti N n B _

/-- **The right composite of the naturality square on a wedge of global sections.** For a unital
homomorphism `g` extending `M̃ ⟶ Ñ` on the degree-one generators, the comparison at `M` followed by
`g` carries the section attached to `m₁ ∧ ⋯ ∧ mₙ` to the ordered product of the degree-one
generators at the global sections of `Ñ` attached to the `f mᵢ`. -/
theorem tildeExteriorPowerIso_natural_right (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N))
    (g : SheafOfModules.GradedAlgebra.UnitalHom A.exterior B.exterior)
    (hg : A.exteriorGenerator ≫ g.app 1 = tilde.map f ≫ B.exteriorGenerator)
    (s : Fin n → ↥M) :
    ((tildeExteriorPowerIso M A n).hom ≫ g.app (n : ℤ)).val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ⊤).hom (exteriorPower.ιMulti ↥R n s)) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => B.exteriorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen N ⊤).hom (f.hom (s i)))) := by
  show (g.app (n : ℤ)).val.app (specGlobalOpen R)
      ((tildeExteriorPowerIso M A n).hom.val.app (specGlobalOpen R) _) = _
  rw [tildeExteriorPowerIso_hom_app_ιMulti]
  refine Eq.trans (SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd g
    (specGlobalOpen R) n _) ?_
  refine congrArg (B.exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n)
    (funext fun i => ?_)
  refine Eq.trans (congrArg (fun k : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶
      B.exterior.piece 1 => k.val.app (specGlobalOpen R) ((tilde.toOpen M ⊤).hom (s i))) hg) ?_
  exact congrArg (B.exteriorGenerator.val.app (specGlobalOpen R))
    (tilde_map_app_toOpen f ⊤ (s i))

/-! ### Naturality -/

/-- **The affine exterior-power comparison is natural.** It respects every unital homomorphism of
exterior algebra sheaves extending the map `M̃ ⟶ Ñ` of generating module sheaves on the
degree-one generators; the universal property of the exterior algebra makes such a homomorphism
unique, so this determines the degree-`n` square. -/
@[stacks 01I8 "exterior_power"]
theorem tildeExteriorPowerIso_natural (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N))
    (g : SheafOfModules.GradedAlgebra.UnitalHom A.exterior B.exterior)
    (hg : A.exteriorGenerator ≫ g.app 1 = tilde.map f ≫ B.exteriorGenerator) :
    tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
          (exteriorPower.map n f.hom)) ≫ (tildeExteriorPowerIso N B n).hom =
      (tildeExteriorPowerIso M A n).hom ≫ g.app (n : ℤ) :=
  hom_ext_ιMulti fun s =>
    (tildeExteriorPowerIso_natural_left f n B s).trans
      (tildeExteriorPowerIso_natural_right f n A B g hg s).symm

/-- **The affine exterior-power comparison is natural, for the canonical induced map.** This is
`Stacks.AffineExteriorPower.tildeExteriorPowerIso_natural` applied to the unital homomorphism
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map` that the universal property produces, whose
degree-`n` component is `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap`. -/
theorem tildeExteriorPowerIso_natural_exteriorPowerMap (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    tilde.map (ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
          (exteriorPower.map n f.hom)) ≫ (tildeExteriorPowerIso N B n).hom =
      (tildeExteriorPowerIso M A n).hom ≫ A.exteriorPowerMap B (tilde.map f) (n : ℤ) :=
  tildeExteriorPowerIso_natural f n A B
    (A.exterior_isExteriorAlgebra.map B.exterior_isExteriorAlgebra (tilde.map f))
    (A.exterior_isExteriorAlgebra.map_app_one B.exterior_isExteriorAlgebra (tilde.map f))

/-! ### Naturality on global sections -/

/-- The naturality square of
`Stacks.AffineExteriorPower.exteriorPowerΓIso` in the orientation its inverse composes in: the
inverse of `Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M` intertwines `⋀ⁿ(f)` with the global sections of `g`. -/
theorem exteriorPowerΓIso_inv_natural (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N))
    (g : SheafOfModules.GradedAlgebra.UnitalHom A.exterior B.exterior)
    (hg : A.exteriorGenerator ≫ g.app 1 = tilde.map f ≫ B.exteriorGenerator) :
    ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
          (exteriorPower.map n f.hom) ≫ (exteriorPowerΓIso N B n).inv =
      (exteriorPowerΓIso M A n).inv ≫ moduleSpecΓFunctor.map (g.app (n : ℤ)) := by
  have hmid := (moduleSpecΓFunctor.map_comp _ _).symm.trans
    ((congrArg moduleSpecΓFunctor.map (tildeExteriorPowerIso_natural f n A B g hg)).trans
      (moduleSpecΓFunctor.map_comp _ _))
  rw [exteriorPowerΓIso_inv, exteriorPowerΓIso_inv, Category.assoc]
  exact (tilde.toTildeΓNatIso.hom.naturality_assoc _ _).trans (congrArg _ hmid)

/-- **The exterior-power assertion of Tag 01I8 is natural on global sections.** The isomorphism
`Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M` carries the global sections of a unital homomorphism of exterior
algebra sheaves extending `M̃ ⟶ Ñ` to `⋀ⁿ(f)`: reading the square left to right, applying `g` in
degree `n` on global sections and then identifying with `⋀ⁿ_R N` is the same as identifying with
`⋀ⁿ_R M` and then applying `⋀ⁿ(f)`. -/
theorem exteriorPowerΓIso_natural (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N))
    (g : SheafOfModules.GradedAlgebra.UnitalHom A.exterior B.exterior)
    (hg : A.exteriorGenerator ≫ g.app 1 = tilde.map f ≫ B.exteriorGenerator) :
    moduleSpecΓFunctor.map (g.app (n : ℤ)) ≫ (exteriorPowerΓIso N B n).hom =
      (exteriorPowerΓIso M A n).hom ≫ ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
        (exteriorPower.map n f.hom) := by
  rw [(Iso.inv_comp_eq _).mp (exteriorPowerΓIso_inv_natural f n A B g hg).symm,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The exterior-power assertion of Tag 01I8 is natural on global sections, for the canonical
induced map.** This is `Stacks.AffineExteriorPower.exteriorPowerΓIso_natural` for the map
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap` that the universal property of
the exterior algebra produces. -/
theorem exteriorPowerΓIso_natural_exteriorPowerMap (n : ℕ)
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M))
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde N)) :
    moduleSpecΓFunctor.map (A.exteriorPowerMap B (tilde.map f) (n : ℤ)) ≫
        (exteriorPowerΓIso N B n).hom =
      (exteriorPowerΓIso M A n).hom ≫ ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥N))
        (exteriorPower.map n f.hom) :=
  exteriorPowerΓIso_natural f n A B
    (A.exterior_isExteriorAlgebra.map B.exterior_isExteriorAlgebra (tilde.map f))
    (A.exterior_isExteriorAlgebra.map_app_one B.exterior_isExteriorAlgebra (tilde.map f))

end Stacks.AffineExteriorPower

end
