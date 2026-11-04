module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemLevelwise
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionLevel
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTower
public import StacksFrontier.RingTheory.AdicCompletion.QuotientRestrictScalars

/-!
# The tower of termwise reductions under change of rings

Let `(C, J)` be a site and `e : A → S` a homomorphism of commutative rings. For a complex `K` of
sheaves of `A`-modules and an `S`-module `L`, the projection formula identifies, termwise,
`K ⊗_A \underline{L}` (with `L` read over `A`) with `(S ⊗_A K) ⊗_S \underline{L}` read over `A`,
naturally in `L`. If `e` is surjective with kernel in `𝔞ᵐ`, the adic quotients `A/𝔞ʲ`, `j ≤ m`,
are the adic quotients `S/(𝔞S)ʲ` read over `A`, so the truncation of the tower of termwise
reductions `j ↦ K ⊗_A \underline{A/𝔞ʲ}` to `j ≤ m` is the restriction of scalars of the tower
`j ↦ (S ⊗_A K) ⊗_S \underline{S/(𝔞S)ʲ}`.

## Main definitions

* `Stacks.ModuleSheaf.restrictScalarsConstantSheafRowFunctorIso`: the termwise projection
  formula `K ⊗_A \underline{L} ≅ (S ⊗_A K) ⊗_S \underline{L}`, natural in the `S`-module `L`.
* `Stacks.ModuleSheaf.rowAdicTowerIsoRestrictScalars`: if the adic quotients of `A` are those of
  `S` read over `A`, the tower of termwise reductions of `K` is the restriction of scalars of that
  of `S ⊗_A K`.
* `Stacks.ModuleSheaf.rowAdicTowerObjIsoOfPowEqBot`: if `𝔟ᵐ = 0`, the term of index `m` of the
  tower of termwise reductions of `U` is `U`.
* `Stacks.ModuleSheaf.extendScalarsConstantSheafComplexIso`: extension of scalars of a constant
  complex is the constant complex on the termwise extension of scalars.
* `Stacks.ModuleSheaf.extendScalarsCompExtendScalarsIso`: extension of scalars along `f` and then
  `g` is extension of scalars along `g ∘ f`.

## Main results

* `Stacks.ModuleSheaf.exists_rowAdicTower_iso_restrictScalars`: the truncated tower of termwise
  reductions along a surjection with kernel in `𝔞ᵐ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type w} [CommRing A]
  [UnivLE.{max u v, w}]

section D

variable {S : Type w} [CommRing S]

variable (J) in
/-- **The termwise projection formula, natural in the coefficients.** For a ring map
`e : A → S` and a complex `K` of sheaves of `A`-modules, the functor
`L ↦ K ⊗_A \underline{L}` on `S`-modules (with `L` read over `A`, the tensor product taken
termwise) is the functor `L ↦ (S ⊗_A K) ⊗_S \underline{L}` read over `A`. -/
def restrictScalarsConstantSheafRowFunctorIso (e : A →+* S)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    ModuleCat.restrictScalars.{w} e ⋙ constantSheaf J (ModuleCat.{w} A) ⋙
        rowFunctor (curriedTensor _) K ≅
      constantSheaf J (ModuleCat.{w} S) ⋙
        rowFunctor (curriedTensor _) (((extendScalars J e).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⋙
        (restrictScalars J e).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsConstantSheafIso J e).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantSheaf J (ModuleCat.{w} S))
      (mapRowFunctorIso (extendScalars J e ⋙ curriedTensor (Sheaf J (ModuleCat.{w} S)))
        (curriedTensor (Sheaf J (ModuleCat.{w} A)))
        (extendScalarsTensorRestrictScalarsIso e) K).symm

variable (J) in
/-- **The tower of termwise reductions under change of rings.** Let `e : A → S` be a ring map and
`𝔞 ⊆ A` an ideal such that the adic quotients `A/𝔞ʲ` are, compatibly with the transition maps,
the adic quotients `S/(𝔞S)ʲ` read over `A`. Then for a complex `K` of sheaves of `A`-modules the
tower `j ↦ K ⊗_A \underline{A/𝔞ʲ}` is the restriction of scalars of the tower
`j ↦ (S ⊗_A K) ⊗_S \underline{S/(𝔞S)ʲ}`. -/
def rowAdicTowerIsoRestrictScalars (e : A →+* S) (𝔞 : Ideal A)
    (α : AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A) ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem S (𝔞.map e) (ModuleCat.of S S) ⋙
        ModuleCat.restrictScalars.{w} e)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    rowAdicTower J 𝔞 K ≅
      rowAdicTower J (𝔞.map e) (((extendScalars J e).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⋙
        (restrictScalars J e).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.isoWhiskerRight α (constantSheaf J (ModuleCat.{w} A) ⋙ rowFunctor (curriedTensor _) K) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictScalarsConstantSheafRowFunctorIso J e K)

/-- **The truncated tower of termwise reductions along a surjection.** Let `e : A → S` be a
surjective ring map whose kernel is contained in `𝔞ᵐ`. For a complex `K` of sheaves of
`A`-modules, the terms `K ⊗_A \underline{A/𝔞ʲ}`, `j ≤ m`, of the tower of termwise reductions
are, compatibly with the transition maps, the restrictions of scalars of the terms
`(S ⊗_A K) ⊗_S \underline{S/(𝔞S)ʲ}`. -/
theorem exists_rowAdicTower_iso_restrictScalars (e : A →+* S) (he : Function.Surjective e)
    (𝔞 : Ideal A) (m : ℕ) (hm : RingHom.ker e ≤ 𝔞 ^ m)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    ∃ ε : ∀ j : ℕ, j ≤ m → ((rowAdicTower J 𝔞 K).obj (op j) ≅
        ((restrictScalars J e).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((rowAdicTower J (𝔞.map e) (((extendScalars J e).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)).obj (op j))),
      ∀ (i j : ℕ) (hij : i ≤ j) (hjm : j ≤ m),
        (rowAdicTower J 𝔞 K).map (homOfLE hij).op ≫ (ε i (hij.trans hjm)).hom =
          (ε j hjm).hom ≫ ((restrictScalars J e).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((rowAdicTower J (𝔞.map e) (((extendScalars J e).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)).map (homOfLE hij).op) :=
  exists_le_iso_comp_of_iso
    (X := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A))
    (Y := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem S (𝔞.map e) (ModuleCat.of S S))
    (T := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem S (𝔞.map e) (ModuleCat.of S S))
    (b := 𝟭 _)
    (restrictScalarsConstantSheafRowFunctorIso J e K ≪≫ (Functor.leftUnitor _).symm) m
    (fun j hj => AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso e he 𝔞 _ rfl j
      (hm.trans (Ideal.pow_le_pow_right hj)))
    (fun _ _ hij _ =>
      AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso_naturality _ _ _ _ _ hij _ _)
    (fun _ _ => Iso.refl _) (fun _ _ _ _ => by simp)

/-- If `𝔟ᵐ = 0`, the reduction `S/𝔟ᵐ` is `S` itself. -/
def adicQuotientModuleSystemObjIsoOfPowEqBot (𝔟 : Ideal S) {m : ℕ} (hm : 𝔟 ^ m = ⊥) :
    (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem S 𝔟 (ModuleCat.of S S)).obj (op m) ≅
      ModuleCat.of S S :=
  (Submodule.quotEquivOfEqBot _ (by simp [hm])).toModuleIso

/-- **The tower of termwise reductions at a nilpotence level.** If `𝔟ᵐ = 0`, the term
`U ⊗_S \underline{S/𝔟ᵐ}` of the tower of termwise reductions of `U` is `U`. -/
def rowAdicTowerObjIsoOfPowEqBot (𝔟 : Ideal S) {m : ℕ} (hm : 𝔟 ^ m = ⊥)
    (U : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ) :
    (rowAdicTower J 𝔟 U).obj (op m) ≅ U :=
  (rowFunctor (curriedTensor _) U).mapIso ((constantSheaf J (ModuleCat.{w} S)).mapIso
      (adicQuotientModuleSystemObjIsoOfPowEqBot 𝔟 hm)) ≪≫
    rowComplexUnitIso J U

/-- The identification `U ⊗_S \underline{S/𝔟ᵐ} ≅ U` for `𝔟ᵐ = 0` is natural in `U`. -/
theorem rowAdicTowerObjIsoOfPowEqBot_hom_naturality (𝔟 : Ideal S) {m : ℕ} (hm : 𝔟 ^ m = ⊥)
    {U V : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ} (f : U ⟶ V) :
    rowComplexMap (curriedTensor _) f _ ≫ (rowAdicTowerObjIsoOfPowEqBot 𝔟 hm V).hom =
      (rowAdicTowerObjIsoOfPowEqBot 𝔟 hm U).hom ≫ f :=
  (rowComplexMap_comp_rowComplexMapRight_assoc _ f _ _).trans
    ((whisker_eq _ (rowComplexUnitIso_hom_naturality J f)).trans (Category.assoc _ _ _).symm)

/-- **Extension of scalars of a constant complex** is the constant complex on the termwise
extension of scalars. -/
def extendScalarsConstantSheafComplexIso (e : A →+* S) (M : CochainComplex (ModuleCat.{w} A) ℤ) :
    ((extendScalars J e).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅
      ((constantSheaf J (ModuleCat.{w} S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{w, w, w} e).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (extendScalarsConstantSheafIso J e).app (M.X p))
    (fun p q _ => ((extendScalarsConstantSheafIso J e).hom.naturality (M.d p q)).symm)

end D

variable (J) in
/-- Restriction of scalars along `g ∘ f` is restriction along `g` followed by restriction along
`f`. -/
def restrictScalarsCompIso {Λ S' : Type w} [CommRing Λ] [CommRing S'] (f : Λ →+* A)
    (g : A →+* S') :
    restrictScalars J (g.comp f) ≅ restrictScalars J g ⋙ restrictScalars J f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Extension of scalars is transitive**: extension of scalars along `f` and then along `g` is
extension of scalars along `g ∘ f`, both being left adjoint to restriction of scalars along
`g ∘ f`. -/
def extendScalarsCompExtendScalarsIso {Λ S' : Type w} [CommRing Λ] [CommRing S'] (f : Λ →+* A)
    (g : A →+* S') :
    extendScalars J f ⋙ extendScalars J g ≅ extendScalars J (g.comp f) :=
  Adjunction.leftAdjointUniq ((extendRestrictScalarsAdj J f).comp (extendRestrictScalarsAdj J g))
    ((extendRestrictScalarsAdj J (g.comp f)).ofNatIsoRight (restrictScalarsCompIso J f g))

end Stacks.ModuleSheaf

end
