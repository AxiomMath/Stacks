module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherentSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeTensorPower
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChangeNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerModelProduct

/-!
# Symmetric powers of associated sheaves on an affine scheme

For a module `M` over a commutative ring `R` and `n : ℕ`, the sheaf associated to the `n`-th
symmetric power `Symⁿ_R M` is canonically the `n`-th symmetric power, in the sense of Stacks
Section 17.21, of the associated sheaf of `M` on `Spec R`.

## Main definitions

* `AlgebraicGeometry.specTildeSymmetricPowerPresheafIso`: the presheaf-level comparison
  `𝒪 ⊗_R Symⁿ_R M ≅ Symⁿ_𝒪(𝒪 ⊗_R M)`, the base-change comparison
  `SymmetricAlgebra.symmetricPowerBaseChange` read over every open.
* `AlgebraicGeometry.tildeSymmetricPowerIso`: the affine symmetric-power comparison
  `(Symⁿ_R M)~ ≅ Symⁿ(M~)`.

## Main results

* `AlgebraicGeometry.tildeSymmetricPowerIso_unit`: in degree zero the comparison carries the
  unit of the algebraic symmetric algebra to the unit of the symmetric algebra sheaf.
* `AlgebraicGeometry.tildeSymmetricPowerIso_generator`: in degree one it carries an algebraic
  degree-one generator to the corresponding generator of the symmetric algebra sheaf.
* `AlgebraicGeometry.tildeSymmetricPowerIso_mul_generator`: multiplication by an algebraic
  degree-one generator is carried to multiplication by the corresponding sheaf generator.
  Together with the degree-zero and degree-one equations this fixes the comparison in every
  degree.
* `AlgebraicGeometry.tildeSymmetricPowerIso_natural`: the comparison is natural in `M`, for any
  unital homomorphism of symmetric algebra sheaves extending `tilde.map f` on degree-one
  generators — the universal property makes such a homomorphism unique, so the statement
  quantified over it is a statement about the canonical one.
* `AlgebraicGeometry.tildeSymmetricPowerIso_hom_prod_ι`: the comparison on the global section
  attached to a product of `n` degree-one generators, which is what the naturality proof
  evaluates both sides on.

## Implementation notes

`M~` is the sheafification of the presheaf `U ↦ 𝒪(U) ⊗_R M`
(`Stacks.AssociatedSheaf.associatedPresheaf`, by Tag 01I7 — the comparison is
`AlgebraicGeometry.tildeAssociatedSheafNatIso`), and
`SheafOfModules.presheafModelSymmetricPowerIso` says that the degree-`n` symmetric power of a
sheaf of modules is the sheafification of the sectionwise degree-`n` symmetric power of *any*
presheaf model of it. So all that is needed is a presheaf isomorphism

`𝒪(U) ⊗_R Symⁿ_R M ≅ Symⁿ_{𝒪(U)}(𝒪(U) ⊗_R M)`,

which is `SymmetricAlgebra.symmetricPowerBaseChange` over each open, natural in the open by
`SymmetricAlgebra.symmetricPowerBaseChange_naturality`. Sheafifying it and composing with the
two gives the comparison.

Specialising Tag 01CG to this presheaf instead would require knowing that the sectionwise
symmetric power carries a locally bijective morphism to a locally bijective one, which is not
available; the presheaf-model statement avoids it.

`Stacks.AssociatedSheaf.hasModuleSheafify` and `moduleSheafifyWEqualsLocallyBijective` are made
local instances, so that the sheafification of presheaves of modules on `Spec R` is available to
instance search in the shape in which `Stacks.AssociatedSheaf.associatedSheaf` is defined;
without that the two spellings of one sheafification do not meet. The results of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresheafModel` are stated over a
variable site, which is what lets them be specialised here at all: at the `Spec R` spelling the
sheaf of rings is built by `sheafCompose` and the local-bijectivity instances its universal
property needs are unreachable to instance search.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AssociatedSheaf
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-- The ordered product of a single degree-one local section is that section. -/
private theorem homogeneousProd_one {C' : Type u} [Category.{u} C'] {O : C'ᵒᵖ ⥤ CommRingCat.{u}}
    {Pc : ℤ → PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (A : Stacks.GradedAlgebra Pc) (X : C'ᵒᵖ) (z : Fin 1 → (Pc 1).obj X) :
    A.homogeneousProd X 1 z = z 0 :=
  eq_of_heq (A.one_mul 1 X (z 0))

/-! ### The presheaf-level comparison -/

section Presheaf

variable (R : CommRingCat.{u}) (X : RingedSpace.{u, u}) (α : ↥R →+* X.presheaf.obj (op ⊤))
  (M : ModuleCat.{u} R) (n : ℕ)

/-- The base-change comparison `𝒪(U) ⊗_R Symⁿ_R M ≅ Symⁿ_{𝒪(U)}(𝒪(U) ⊗_R M)` over one open.

The two sides are the sections over `U` of the two presheaves compared by
`specTildeSymmetricPowerPresheafIso`; the identification is `symmetricPowerBaseChange` with no
retyping, because the sections of the sectionwise symmetric power are the symmetric power of the
sections. -/
noncomputable def specTildeSymmetricPowerPointIso (U : (Opens X.carrier)ᵒᵖ) :
    (associatedPresheaf X α (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M))).obj U ≅
      (PresheafOfModules.symPowInt (n : ℤ)
        (associatedPresheaf X α M)).obj U := by
  letI : Algebra ↥R ↥(X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
  exact (SymmetricAlgebra.symmetricPowerBaseChange ↥R ↥(X.presheaf.obj U) ↥M n).toModuleIso

/-- The presheaf-level comparison: the presheaf `U ↦ 𝒪(U) ⊗_R Symⁿ_R M` whose sheafification is
`(Symⁿ_R M)~` is the sectionwise degree-`n` symmetric power of the presheaf `U ↦ 𝒪(U) ⊗_R M`
whose sheafification is `M~`. -/
noncomputable def specTildeSymmetricPowerPresheafIso :
    associatedPresheaf X α (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ≅
      PresheafOfModules.symPowInt (n : ℤ) (associatedPresheaf X α M) := by
  refine PresheafOfModules.isoMk
    (fun U ↦ specTildeSymmetricPowerPointIso R X α M n U) (fun {U V} f ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_)
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg (fun z ↦ z + _) hx).trans
        ((congrArg (fun z ↦ _ + z) hy).trans (map_add _ x y).symm))
  | tmul a x =>
      refine Subtype.ext ?_
      let : Algebra ↥R ↥(X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
      let : Algebra ↥R ↥(X.presheaf.obj V) := ((globalSectionsMap X α).app V).hom.toAlgebra
      refine (SymmetricAlgebra.symmetricPowerBaseChange_naturality
        (R := ↥R) (A := ↥(X.presheaf.obj U)) (B := ↥(X.presheaf.obj V)) (M := ↥M)
        (φ := ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf).map f).hom) ?_
        (u := (associatedPresheaf X α M).restrictₛₗ f) ?_ n a x).symm
      · exact fun r => (congrArg
          (fun g : (constantRingPresheaf X ↥R).obj U ⟶ X.presheaf.obj V =>
            (ConcreteCategory.hom g) r) ((globalSectionsMap X α).naturality f)).symm
      · exact fun m => congrArg (fun b : ↥(X.presheaf.obj V) => b ⊗ₜ[↥R] m)
          (map_one (X.presheaf.map f).hom)

end Presheaf

/-! ### The comparison -/

section Comparison

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ)

/-- The presheaf `U ↦ 𝒪(U) ⊗_R M` on `Spec R`, whose sheafification is `M~`. -/
noncomputable abbrev specTildePresheaf :
    PresheafOfModules.{u}
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (Spec R).toRingedSpace.presheaf) :=
  associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M

/-- `M~` presented as the sheafification of `specTildePresheaf`: the comparison of Tag 01I7. -/
noncomputable abbrev specTildeModel : tilde M ≅ SheafOfModules.sheafifyModulePresheaf
    (Opens.grothendieckTopology ↥(Spec R)) (specTildePresheaf R M) :=
  (tildeAssociatedSheafNatIso R).val.app M

/-- The associated sheaf of the `n`-th symmetric power is canonically the `n`-th symmetric power
of the associated sheaf, the symmetric-power part of [Stacks, Tag 01I8]. -/
noncomputable def tildeSymmetricPowerIso :
    tilde (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ≅
      (specTildeAlgebras R M).symmetricPower n :=
  (tildeAssociatedSheafNatIso R).val.app
      (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ≪≫
    (PresheafOfModules.sheafification
        (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)).mapIso
      (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom M n) ≪≫
    SheafOfModules.presheafModelSymmetricPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M) (n : ℤ)

/-- The presheaf-model comparison on the unit-image of a global section of the sectionwise
symmetric power: the map every equation below is stated through. -/
private noncomputable def specTildeModelCmp (d : ℤ)
    (z : (PresheafOfModules.symPowInt d (specTildePresheaf R M)).obj
      (specGlobalOpen R)) :
    ((specTildeAlgebras R M).symmetric.piece d).val.obj (specGlobalOpen R) :=
  (SheafOfModules.presheafModelSymmetricPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
      d).hom.val.app (specGlobalOpen R)
    (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
      (PresheafOfModules.symPowInt d (specTildePresheaf R M)))
      (specGlobalOpen R) z)

/-- The global section `1 ⊗ y` of the presheaf model `U ↦ 𝒪(U) ⊗_R N` of `N~`. -/
noncomputable def specTildePresheafUnit (N : ModuleCat.{u} R) (y : N) :
    (specTildePresheaf R N).obj (specGlobalOpen R) := by
  letI : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
    ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
      (specGlobalOpen R)).hom.toAlgebra
  exact (1 : ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))) ⊗ₜ[↥R] y

/-- The canonical global section of `N~` attached to `y : N` is the unit-image of `1 ⊗ y`. -/
theorem tildeModel_toOpen (N : ModuleCat.{u} R) (y : N) :
    (specTildeModel R N).hom.val.app (specGlobalOpen R) ((tilde.toOpen N ⊤).hom y) =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
          (specTildePresheaf R N)) (specGlobalOpen R) (specTildePresheafUnit R N y) :=
  (tildeAssociatedSheafNatIso R).property N y

/-- The inverse of the comparison of Tag 01I7 carries the unit-image of `1 ⊗ y` back to the
canonical global section of `N~`. -/
theorem tildeModel_inv_unit (N : ModuleCat.{u} R) (y : N) :
    (specTildeModel R N).inv.val.app (specGlobalOpen R)
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
          (specTildePresheaf R N)) (specGlobalOpen R) (specTildePresheafUnit R N y)) =
      (tilde.toOpen N ⊤).hom y :=
  Eq.trans
    (congrArg ((specTildeModel R N).inv.val.app (specGlobalOpen R))
      (tildeModel_toOpen R N y).symm)
    (congrArg (fun k : tilde N ⟶ tilde N => k.val.app (specGlobalOpen R)
      ((tilde.toOpen N ⊤).hom y)) (specTildeModel R N).hom_inv_id)

/-- The presheaf-level comparison on the global section `1 ⊗ x`: it is the base-change
comparison of symmetric powers at the ring of global sections. -/
private theorem specTildeSymmetricPowerPresheafIso_unit
    (x : SymPow.symmetricPower n ↥R ↥M) :
    letI : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
      ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
        (specGlobalOpen R)).hom.toAlgebra
    PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x) =
      SymmetricAlgebra.symmetricPowerBaseChange ↥R
        ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M n
        ((1 : ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))) ⊗ₜ[↥R] x) := rfl

/-- The same equation read in the symmetric algebra of the sections, which is the shape the
multiplicative equations are proved in. -/
private theorem specTildeSymmetricPowerPresheafIso_unit_val
    (x : SymPow.symmetricPower n ↥R ↥M) :
    letI : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
      ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
        (specGlobalOpen R)).hom.toAlgebra
    PresheafOfModules.symPowIntVal (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R
            (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
          (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x)) =
      (SymmetricAlgebra.symmetricPowerBaseChange ↥R
        ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M n
        ((1 : ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))) ⊗ₜ[↥R] x) :
          SymmetricAlgebra ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
            (↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ⊗[↥R] ↥M)) := rfl

/-- The comparison on a global section of the algebraic symmetric power: the presheaf-level
comparison at `1 ⊗ x`, followed by the sheafification unit and the presheaf-model
comparison. -/
private theorem tildeSymmetricPowerIso_hom_toOpen (x : SymPow.symmetricPower n ↥R ↥M) :
    (tildeSymmetricPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ⊤).hom x) =
      specTildeModelCmp R M (n : ℤ)
        (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R
            (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
          (specTildePresheafUnit R
            (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x)) :=
  congrArg
    ((SheafOfModules.presheafModelSymmetricPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
      (n : ℤ)).hom.val.app (specGlobalOpen R))
    (Eq.trans
      (congrArg (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafification
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)).map
            (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
              (Scheme.ΓSpecIso R).inv.hom M n).hom).val (specGlobalOpen R))
        (tildeModel_toOpen R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x))
      (PresheafOfModules.unit_naturality_apply
        (α := 𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
        (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x)))

/-- A morphism out of `M~` is determined by its value on the canonical global sections. -/
private theorem tildeHomEquiv_apply (F : (Spec R).Modules) (h : tilde M ⟶ F) (m : M) :
    (((tilde.adjunction (R := R)).homEquiv M F) h).hom m =
      h.val.app (specGlobalOpen R) ((tilde.toOpen M ⊤).hom m) := rfl

/-- The presheaf-level comparison on the global section `1 ⊗ (ι m₁ ⋯ ι mₙ)`: it is the product
of the sectionwise degree-one generators at the sections `1 ⊗ mᵢ`. -/
private theorem specTildeSymmetricPowerPresheafIso_unit_prod_ι (s : Fin n → ↥M) :
    PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M))
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i), SymmetricAlgebra.prod_ι_mem ↥R s⟩) =
      (⟨∏ i : Fin n, SymmetricAlgebra.ι
            ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
            ((specTildePresheaf R M).obj (specGlobalOpen R))
            (specTildePresheafUnit R M (s i)),
          SymmetricAlgebra.prod_ι_mem _ _⟩ :
            SymPow.symmetricPower n
              ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
              ((specTildePresheaf R M).obj (specGlobalOpen R))) := by
  let : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
    ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
      (specGlobalOpen R)).hom.toAlgebra
  refine Subtype.ext ?_
  refine Eq.trans (SymmetricAlgebra.symmetricPowerBaseChange_tmul_prod_ι ↥R
    ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M n 1 s) ?_
  exact one_smul ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
    (∏ i : Fin n, SymmetricAlgebra.ι
      ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
      ((specTildePresheaf R M).obj (specGlobalOpen R))
      (specTildePresheafUnit R M (s i)))

/-- The comparison on a product of degree-one generators: the global section of `(Symⁿ_R M)~`
attached to `ι m₁ ⋯ ι mₙ` is carried to the ordered product, in `Sym(M~)`, of the degree-one
generators at the global sections attached to the `mᵢ`. Those products span the symmetric power,
so this determines the comparison. -/
theorem tildeSymmetricPowerIso_hom_prod_ι (s : Fin n → ↥M) :
    (tildeSymmetricPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ⊤).hom
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i), SymmetricAlgebra.prod_ι_mem ↥R s⟩) =
      (specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra.homogeneousProd
        (specGlobalOpen R) n
        (fun i => (specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (s i))) := by
  refine Eq.trans (tildeSymmetricPowerIso_hom_toOpen R M n _) ?_
  refine Eq.trans (congrArg (specTildeModelCmp R M (n : ℤ))
    (specTildeSymmetricPowerPresheafIso_unit_prod_ι R M n s)) ?_
  refine Eq.trans (SheafOfModules.presheafModelSymmetricPowerIso_prod_ι
    (Opens.grothendieckTopology ↥(Spec R)) (specTildePresheaf R M) (specTildeAlgebras R M)
    (specTildeModel R M) n (specGlobalOpen R)
    (fun i => specTildePresheafUnit R M (s i))) ?_
  exact congrArg ((specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra.homogeneousProd
      (specGlobalOpen R) n)
    (funext fun i => congrArg
      ((specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R))
      (tildeModel_inv_unit R M (s i)))

/-- The adjoint of the comparison on a product of degree-one generators: `tildeHomEquiv_apply`
followed by `tildeSymmetricPowerIso_hom_prod_ι`. -/
private theorem homEquiv_tildeSymmetricPowerIso_prod_ι (s : Fin n → ↥M) :
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M))
      ((specTildeAlgebras R M).symmetricPower n))
      (tildeSymmetricPowerIso R M n).hom).hom
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i), SymmetricAlgebra.prod_ι_mem ↥R s⟩ =
      (specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra.homogeneousProd
        (specGlobalOpen R) n
        (fun i => (specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (s i))) :=
  (tildeHomEquiv_apply R _ _ _ _).trans (tildeSymmetricPowerIso_hom_prod_ι R M n s)

/-- In degree zero the comparison takes the algebraic unit to the unit of the symmetric algebra
sheaf, part of the symmetric-power clause of [Stacks, Tag 01I8]. -/
theorem tildeSymmetricPowerIso_unit :
    let x : SymPow.symmetricPower 0 ↥R ↥M := ⟨1, by
      change (1 : SymmetricAlgebra ↥R ↥M) ∈
        (LinearMap.range (SymmetricAlgebra.ι ↥R ↥M)) ^ 0
      simp⟩
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of ↥R (SymPow.symmetricPower 0 ↥R ↥M))
      ((specTildeAlgebras R M).symmetricPower 0))
      (tildeSymmetricPowerIso R M 0).hom).hom x =
        (specTildeAlgebras R M).symmetric.one.eval (specGlobalOpen R) := by
  intro x
  have hx : x = ⟨∏ i : Fin 0, SymmetricAlgebra.ι ↥R ↥M (i.elim0 : ↥M),
      SymmetricAlgebra.prod_ι_mem ↥R _⟩ := Subtype.ext (by simp [x])
  rw [hx]
  exact homEquiv_tildeSymmetricPowerIso_prod_ι R M 0 _

/-- In degree one the comparison takes an algebraic degree-one generator to the corresponding
generator of the symmetric algebra sheaf, part of the symmetric-power clause of
[Stacks, Tag 01I8]. -/
theorem tildeSymmetricPowerIso_generator (m : M) :
    let x : SymPow.symmetricPower 1 ↥R ↥M :=
      ⟨SymmetricAlgebra.ι ↥R ↥M m, by
        change SymmetricAlgebra.ι ↥R ↥M m ∈
          (LinearMap.range (SymmetricAlgebra.ι ↥R ↥M)) ^ 1
        simp⟩
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of ↥R (SymPow.symmetricPower 1 ↥R ↥M))
      ((specTildeAlgebras R M).symmetricPower 1))
      (tildeSymmetricPowerIso R M 1).hom).hom x =
        ((specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R))
          ((tilde.toOpen M ⊤).hom m) := by
  intro x
  have hx : x = ⟨∏ _i : Fin 1, SymmetricAlgebra.ι ↥R ↥M m,
      SymmetricAlgebra.prod_ι_mem ↥R _⟩ := Subtype.ext (by simp [x])
  rw [hx]
  exact (homEquiv_tildeSymmetricPowerIso_prod_ι R M 1 fun _ => m).trans
    (homogeneousProd_one (specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra
      (specGlobalOpen R) _)

/-- The degree-one generator of `Sym(M~)` at the global section attached to `m`, read through
the presheaf model: it is the comparison applied to the unit-image of the sectionwise generator
at `1 ⊗ m`. -/
private theorem symmetricGenerator_toOpen (m : M) :
    (specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom m) =
      specTildeModelCmp R M 1
        (PresheafOfModules.Hom.app
          (PresheafOfModules.symPowIntGen (specTildePresheaf R M))
          (specGlobalOpen R) (specTildePresheafUnit R M m)) :=
  Eq.trans
    (congrArg ((specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R))
      (tildeModel_inv_unit R M m).symm)
    (SheafOfModules.presheafModelSymmetricPowerIso_gen_unit
      (Opens.grothendieckTopology ↥(Spec R)) (specTildePresheaf R M) (specTildeAlgebras R M)
      (specTildeModel R M) (specGlobalOpen R) (specTildePresheafUnit R M m)).symm

/-- The multiplication of `Sym(M~)` read through the presheaf model, stated with the two factors
given by hypotheses so that no rewriting inside the graded multiplication is needed. -/
private theorem specTildeModel_mul (i j : ℤ)
    (a : (PresheafOfModules.symPowInt i (specTildePresheaf R M)).obj
      (specGlobalOpen R))
    (b : (PresheafOfModules.symPowInt j (specTildePresheaf R M)).obj
      (specGlobalOpen R))
    (u : ((specTildeAlgebras R M).symmetric.piece i).val.obj (specGlobalOpen R))
    (v : ((specTildeAlgebras R M).symmetric.piece j).val.obj (specGlobalOpen R))
    (hu : u = specTildeModelCmp R M i a) (hv : v = specTildeModelCmp R M j b) :
    ((specTildeAlgebras R M).symmetric.mul i j).app (specGlobalOpen R) u v =
      specTildeModelCmp R M (i + j)
        (((PresheafOfModules.symPowIntGradedAlgebra (specTildePresheaf R M)).mul i j).app
          (specGlobalOpen R) a b) := by
  subst hu
  subst hv
  refine Eq.trans (SheafOfModules.presheafModelSymmetricPowerIso_mul
    (Opens.grothendieckTopology ↥(Spec R)) (specTildePresheaf R M) (specTildeAlgebras R M)
    (specTildeModel R M) i j (specGlobalOpen R)
    (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
      (PresheafOfModules.symPowInt i (specTildePresheaf R M)))
      (specGlobalOpen R) a)
    (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
      (PresheafOfModules.symPowInt j (specTildePresheaf R M)))
      (specGlobalOpen R) b)).symm ?_
  exact congrArg
    ((SheafOfModules.presheafModelSymmetricPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
      (i + j)).hom.val.app (specGlobalOpen R))
    ((PresheafOfModules.symPowIntGradedAlgebra (specTildePresheaf R M)).sheafify_mul_unit
      (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
      i j (specGlobalOpen R) a b)

/-- The multiplication equation read entirely inside the presheaf model: the presheaf-level
comparison at the unit-image of `1 ⊗ (ι m) ⋅ x` is the product, in the sectionwise symmetric
algebra of `U ↦ 𝒪(U) ⊗_R M`, of the degree-one generator at `1 ⊗ m` with the comparison at
`1 ⊗ x`. The two degrees `n + 1` and `1 + n` are not syntactically equal, so this is an `HEq`;
`tildeSymmetricPowerIso_mul_generator` is this equation transported through
`specTildeModelCmp`. -/
private theorem specTildeModelCmp_heq_mul_gen (m : M)
    (x : SymPow.symmetricPower n ↥R ↥M) :
    HEq
      (specTildeModelCmp R M ((n + 1 : ℕ) : ℤ)
        (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R
            (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M (n + 1)).hom
            (specGlobalOpen R)
          (specTildePresheafUnit R
            (ModuleCat.of ↥R (SymPow.symmetricPower (n + 1) ↥R ↥M))
            (SymPow.symMulMap n (LinearMap.id : ↥M →ₗ[↥R] ↥M) (m ⊗ₜ[↥R] x)))))
      (specTildeModelCmp R M (1 + (n : ℤ))
        (((PresheafOfModules.symPowIntGradedAlgebra (specTildePresheaf R M)).mul 1
            (n : ℤ)).app (specGlobalOpen R)
          (PresheafOfModules.Hom.app
            (PresheafOfModules.symPowIntGen (specTildePresheaf R M))
            (specGlobalOpen R) (specTildePresheafUnit R M m))
          (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R
              (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
            (specTildePresheafUnit R
              (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x)))) := by
  let : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
    ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
      (specGlobalOpen R)).hom.toAlgebra
  have hdeg : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
  refine Stacks.heq_apply
    (fun d : ℤ => ((PresheafOfModules.symPowInt d
      (specTildePresheaf R M)).obj (specGlobalOpen R) : Type u))
    (fun d : ℤ => (((specTildeAlgebras R M).symmetric.piece d).val.obj
      (specGlobalOpen R) : Type u))
    (specTildeModelCmp R M) hdeg ?_
  refine PresheafOfModules.symPowInt_heq_of_degree_eq (specTildePresheaf R M) hdeg _ _ ?_
  refine Eq.trans (specTildeSymmetricPowerPresheafIso_unit_val R M (n + 1)
    (SymPow.symMulMap n (LinearMap.id : ↥M →ₗ[↥R] ↥M) (m ⊗ₜ[↥R] x))) ?_
  refine Eq.trans (SymmetricAlgebra.symmetricPowerBaseChange_tmul_mul_ι
    (R := ↥R) (A := ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)))
    (M := ↥M) n m x) ?_
  refine Eq.trans (congrArg (fun z : SymmetricAlgebra
      ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
      (↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ⊗[↥R] ↥M) =>
    SymmetricAlgebra.ι ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
        (↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ⊗[↥R] ↥M)
        ((1 : ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))) ⊗ₜ[↥R] m) * z)
    (specTildeSymmetricPowerPresheafIso_unit_val R M n x).symm) ?_
  refine Eq.trans ?_ (congrArg (fun k : Stacks.BilinearMap
      (PresheafOfModules.symPowInt 1 (specTildePresheaf R M))
      (PresheafOfModules.symPowInt (n : ℤ) (specTildePresheaf R M))
      (PresheafOfModules.symPowInt (1 + (n : ℤ)) (specTildePresheaf R M)) =>
    PresheafOfModules.symPowIntVal (k.app (specGlobalOpen R) _ _))
    (PresheafOfModules.symPowIntGradedAlgebra_mul (specTildePresheaf R M)
      1 (n : ℤ)).symm)
  refine Eq.trans ?_ (PresheafOfModules.symPowIntVal_mul (specTildePresheaf R M)
    1 (n : ℤ) (specGlobalOpen R)
    (PresheafOfModules.Hom.app
      (PresheafOfModules.symPowIntGen (specTildePresheaf R M))
      (specGlobalOpen R) (specTildePresheafUnit R M m))
    (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
      (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x))).symm
  exact congrArg (fun z : SymmetricAlgebra
      ↥(((Spec R).toRingedSpace.presheaf ⋙ forget₂ CommRingCat RingCat).obj (specGlobalOpen R))
      ((specTildePresheaf R M).obj (specGlobalOpen R)) =>
    z * PresheafOfModules.symPowIntVal (PresheafOfModules.Hom.app
          (specTildeSymmetricPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
        (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x)))
    (PresheafOfModules.symPowIntVal_gen (specTildePresheaf R M)
      (specGlobalOpen R) (specTildePresheafUnit R M m)).symm

/-- The comparison in degree `n + 1` takes multiplication by an algebraic degree-one generator
to multiplication by the corresponding sheaf generator, part of the symmetric-power clause of
[Stacks, Tag 01I8]. Together with the degree-zero and degree-one equations this fixes the
comparison in every degree. -/
theorem tildeSymmetricPowerIso_mul_generator (m : M) (x : SymPow.symmetricPower n ↥R ↥M) :
    HEq
      ((((tilde.adjunction (R := R)).homEquiv
        (ModuleCat.of ↥R (SymPow.symmetricPower (n + 1) ↥R ↥M))
        ((specTildeAlgebras R M).symmetricPower (n + 1)))
        (tildeSymmetricPowerIso R M (n + 1)).hom).hom
          (SymPow.symMulMap n (LinearMap.id : ↥M →ₗ[↥R] ↥M) (m ⊗ₜ[↥R] x)))
      (((specTildeAlgebras R M).symmetric.mul 1 (n : ℤ)).app (specGlobalOpen R)
          (((specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R))
            ((tilde.toOpen M ⊤).hom m))
          ((tildeSymmetricPowerIso R M n).hom.val.app (specGlobalOpen R)
            ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ⊤).hom x))) := by
  -- Both sides are values of `specTildeModelCmp`: the left one by the comparison on a global
  -- section, the right one because the multiplication of `Sym(M~)` is the one of the model.
  have hleft := Eq.trans
    (tildeHomEquiv_apply R (ModuleCat.of ↥R (SymPow.symmetricPower (n + 1) ↥R ↥M))
      ((specTildeAlgebras R M).symmetricPower (n + 1))
      (tildeSymmetricPowerIso R M (n + 1)).hom
      (SymPow.symMulMap n (LinearMap.id : ↥M →ₗ[↥R] ↥M) (m ⊗ₜ[↥R] x)))
    (tildeSymmetricPowerIso_hom_toOpen R M (n + 1)
      (SymPow.symMulMap n (LinearMap.id : ↥M →ₗ[↥R] ↥M) (m ⊗ₜ[↥R] x)))
  have hright := specTildeModel_mul R M 1 (n : ℤ)
    (PresheafOfModules.Hom.app
      (PresheafOfModules.symPowIntGen (specTildePresheaf R M))
      (specGlobalOpen R) (specTildePresheafUnit R M m))
    (PresheafOfModules.Hom.app (specTildeSymmetricPowerPresheafIso R
        (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M n).hom (specGlobalOpen R)
      (specTildePresheafUnit R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) x))
    _ _ (symmetricGenerator_toOpen R M m) (tildeSymmetricPowerIso_hom_toOpen R M n x)
  exact HEq.trans (heq_of_eq hleft)
    (HEq.trans (specTildeModelCmp_heq_mul_gen R M n m x) (heq_of_eq hright.symm))

end Comparison

/-! ### Naturality -/

section Naturality

variable (R : CommRingCat.{u}) {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ)

/-- `tilde.map` on the canonical global sections. -/
private theorem tilde_map_toOpen_apply {X Y : ModuleCat.{u} R} (h : X ⟶ Y) (x : X) :
    (tilde.map h).val.app (specGlobalOpen R) ((tilde.toOpen X ⊤).hom x) =
      (tilde.toOpen Y ⊤).hom (h.hom x) :=
  congrArg (fun k => k.hom x) (tilde.toOpen_map_app h ⊤)

/-- `Symⁿ(f)` on a product of degree-one generators. -/
private theorem symMap_prod_ι (s : Fin n → ↥M) :
    SymPow.symMap n f.hom
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i), SymmetricAlgebra.prod_ι_mem ↥R s⟩ =
      (⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥N (f.hom (s i)),
        SymmetricAlgebra.prod_ι_mem ↥R _⟩ : SymPow.symmetricPower n ↥R ↥N) := by
  refine Subtype.ext ?_
  refine Eq.trans (SymPow.symMap_coe n f.hom _) ?_
  refine Eq.trans (map_prod (SymPow.symAlgMap f.hom)
    (fun i : Fin n => SymmetricAlgebra.ι ↥R ↥M (s i)) Finset.univ) ?_
  exact Finset.prod_congr rfl fun i _ => SymPow.symAlgMap_ι f.hom (s i)

/-- A unital homomorphism of symmetric algebra sheaves commutes with the ordered product of
degree-one local sections. -/
private theorem unitalHom_homogeneousProd
    (g : SheafOfModules.GradedAlgebra.UnitalHom (specTildeAlgebras R M).symmetric
      (specTildeAlgebras R N).symmetric)
    (z : Fin n → ((specTildeAlgebras R M).symmetric.piece 1).val.obj (specGlobalOpen R)) :
    (g.app (n : ℤ)).val.app (specGlobalOpen R)
        ((specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra.homogeneousProd
          (specGlobalOpen R) n z) =
      (specTildeAlgebras R N).symmetric.toPresheafGradedAlgebra.homogeneousProd
        (specGlobalOpen R) n
        (fun i => (g.app 1).val.app (specGlobalOpen R) (z i)) :=
  (specTildeAlgebras R M).symmetric.toPresheafGradedAlgebra.homogeneousProd_map
    (specTildeAlgebras R N).symmetric.toPresheafGradedAlgebra (specGlobalOpen R)
    (fun d y => (g.app d).val.app (specGlobalOpen R) y)
    (g.map_one (specGlobalOpen R))
    (fun i j x y => g.map_mul i j (specGlobalOpen R) x y) n z

/-- The affine symmetric-power comparison respects every unital homomorphism of symmetric
algebra sheaves extending the map of the generating module sheaves, part of the symmetric-power
clause of [Stacks, Tag 01I8]. The universal property of the symmetric algebra makes such a
homomorphism unique, so the statement quantified over it is a statement about the canonical one.
Both sides are computed on a product of `n` degree-one generators, which suffices because those
span. -/
theorem tildeSymmetricPowerIso_natural
    (g : SheafOfModules.GradedAlgebra.UnitalHom (specTildeAlgebras R M).symmetric
      (specTildeAlgebras R N).symmetric)
    (hg : (specTildeAlgebras R M).symmetricGenerator ≫ g.app 1 =
        tilde.map f ≫ (specTildeAlgebras R N).symmetricGenerator) :
    tilde.map (ModuleCat.ofHom (SymPow.symMap n f.hom)) ≫
        (tildeSymmetricPowerIso R N n).hom =
      (tildeSymmetricPowerIso R M n).hom ≫ g.app (n : ℤ) := by
  have hgpt : ∀ m : ↥M, (g.app 1).val.app (specGlobalOpen R)
      ((specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom m)) =
      (specTildeAlgebras R N).symmetricGenerator.val.app (specGlobalOpen R)
        ((tilde.toOpen N ⊤).hom (f.hom m)) := fun m =>
    Eq.trans
      (congrArg (fun k : tilde M ⟶ (specTildeAlgebras R N).symmetric.piece 1 =>
        k.val.app (specGlobalOpen R) ((tilde.toOpen M ⊤).hom m)) hg)
      (congrArg ((specTildeAlgebras R N).symmetricGenerator.val.app (specGlobalOpen R))
        (tilde_map_toOpen_apply R f m))
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  refine SymPow.ext_of_prod_ι fun s => ?_
  refine Eq.trans (tildeHomEquiv_apply R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) _ _ _) ?_
  refine Eq.trans ?_
    (tildeHomEquiv_apply R (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) _ _ _).symm
  change (tildeSymmetricPowerIso R N n).hom.val.app (specGlobalOpen R)
      ((tilde.map (ModuleCat.ofHom (SymPow.symMap n f.hom))).val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ⊤).hom
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i),
            SymmetricAlgebra.prod_ι_mem ↥R s⟩)) =
    (g.app (n : ℤ)).val.app (specGlobalOpen R)
      ((tildeSymmetricPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥M)) ⊤).hom
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ↥R ↥M (s i),
            SymmetricAlgebra.prod_ι_mem ↥R s⟩))
  refine Eq.trans (congrArg ((tildeSymmetricPowerIso R N n).hom.val.app (specGlobalOpen R))
    (Eq.trans (tilde_map_toOpen_apply R (ModuleCat.ofHom (SymPow.symMap n f.hom)) _)
      (congrArg ((tilde.toOpen (ModuleCat.of ↥R (SymPow.symmetricPower n ↥R ↥N)) ⊤).hom)
        (symMap_prod_ι R f n s)))) ?_
  refine Eq.trans (tildeSymmetricPowerIso_hom_prod_ι R N n (fun i => f.hom (s i))) ?_
  refine Eq.trans ?_ (congrArg ((g.app (n : ℤ)).val.app (specGlobalOpen R))
    (tildeSymmetricPowerIso_hom_prod_ι R M n s)).symm
  refine Eq.trans ?_ (unitalHom_homogeneousProd R n g
    (fun i => (specTildeAlgebras R M).symmetricGenerator.val.app (specGlobalOpen R)
      ((tilde.toOpen M ⊤).hom (s i)))).symm
  exact congrArg
    ((specTildeAlgebras R N).symmetric.toPresheafGradedAlgebra.homogeneousProd
      (specGlobalOpen R) n)
    (funext fun i => (hgpt (s i)).symm)

end Naturality

end AlgebraicGeometry

end
