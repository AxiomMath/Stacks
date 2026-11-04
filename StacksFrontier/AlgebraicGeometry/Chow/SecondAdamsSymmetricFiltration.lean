module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsTensorSquare
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSquaresFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricSquareFiltration
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# The filtration relation for `Sym²` in `K₀(Vect(X))`

Let `X` be a scheme and `0 → ℰ --f--> ℱ --g--> 𝒢 → 0` a short exact sequence of finite locally
free `𝒪_X`-modules. The proof of Stacks Tag 0FEJ filters `Sym² ℱ` in three steps with graded
pieces `Sym² ℰ`, `ℰ ⊗ 𝒢` and `Sym² 𝒢`, which gives

`[Sym² ℱ] = [Sym² ℰ] + [ℰ ⊗ 𝒢] + [Sym² 𝒢]`

in `K₀(Vect(X))`; this is the field
`AlgebraicGeometry.VectorBundleKZero.SquarePowersData.classOf_sym_shortExact`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.classOf_sym_shortExact_of_isFiniteLocallyFree`: the relation
  `[Sym² ℱ] = [Sym² ℰ] + [ℰ ⊗ 𝒢] + [Sym² 𝒢]`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_alt_shortExact_of_isFiniteLocallyFree`: the relation
  `[⋀² ℱ] = [⋀² ℰ] + [ℰ ⊗ 𝒢] + [⋀² 𝒢]`.
* `AlgebraicGeometry.VectorBundleKZero.SquarePowersData.of_classOf_sym_tensor`:
  `SquarePowersData X` given the symmetric product relation.

## Proof outline

Write `μ_ℱ : ℰ ⊗ Sym¹ ℱ ⟶ Sym² ℱ` and `μ_ℰ : ℰ ⊗ Sym¹ ℰ ⟶ Sym² ℰ` for the multiplications and `𝒦`
for the kernel of `Sym²(g) : Sym² ℱ ⟶ Sym² 𝒢`. Three short exact sequences of finite locally free
modules are used:

* `0 → 𝒦 → Sym² ℱ → Sym² 𝒢 → 0`, since `Sym²(g)` is an epimorphism (Tag 01CJ);
* `0 → ker μ_ℱ → ℰ ⊗ Sym¹ ℱ → 𝒦 → 0`, since `μ_ℱ` maps onto `𝒦` (Tag 01CJ again);
* `0 → ker μ_ℰ → ℰ ⊗ Sym¹ ℰ → Sym² ℰ → 0`, since `μ_ℰ` is an epimorphism.

The two kernels are isomorphic
(`SheafOfModules.SymSquareFiltration.kernelMulIso`), and `Sym¹ ℳ ≅ ℳ`
(`SheafOfModules.SymSquareFiltration.isIso_generator`). The kernels are finite locally free as
kernels of epimorphisms between finite locally free modules
(`AlgebraicGeometry.isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree`). The relation is
then arithmetic in the ring `K₀(Vect(X))`:
`[𝒦] = [ℰ][ℱ] - [ker μ_ℰ] = [ℰ][ℱ] - [ℰ]² + [Sym² ℰ] = [ℰ][𝒢] + [Sym² ℰ]`.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FiniteLocallyFree TopologicalSpace

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X : Scheme.{u}}

/-- A module finite locally free in the sense of `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`
is finite locally free in the sense of `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`. -/
theorem isFiniteLocallyFree_toSheaf {M : X.Modules}
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M :=
  @Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree X M hM

/-- A module finite locally free in the sense of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` is finite locally free in the sense of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`. -/
theorem isFiniteLocallyFree_ofSheaf {M : X.Modules}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      M) : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M :=
  @Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree X M hM

/-- The kernel of an epimorphism between finite locally free modules is finite locally free. -/
theorem isFiniteLocallyFree_kernel {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (kernel p) :=
  isFiniteLocallyFree_ofSheaf (isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree p
    (isFiniteLocallyFree_toSheaf hM) (isFiniteLocallyFree_toSheaf hN))

/-- The isomorphism `ℰ ⊗ Sym¹ ℱ ≅ ℰ ⊗ ℱ` induced by the generator `ℱ ≅ Sym¹ ℱ` of the
symmetric algebra of `ℱ`. -/
def tensorSymOneIso (E F : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj
        ((SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) F).symmetric.piece
          ((1 : ℕ) : ℤ)) ≅
      Scheme.Modules.tensorObjRingedSpace X E F :=
  haveI := SheafOfModules.SymSquareFiltration.isIso_generator
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) F).symmetricGenerator
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      F).symmetric_isSymmetricAlgebra
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).mapIso
    (asIso (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      F).symmetricGenerator).symm

/-- If `ℰ` and `ℱ` are finite locally free, then so is `ℰ ⊗ Sym¹ ℱ`. -/
theorem isFiniteLocallyFree_tensorSymOne (E F : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj
        ((SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) F).symmetric.piece
          ((1 : ℕ) : ℤ))) :=
  @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ (tensorSymOneIso E F).symm
    (@isFiniteLocallyFree_tensorObj X E F hE hF)

/-- For finite locally free `ℰ` and `ℱ`, `[ℰ ⊗ Sym¹ ℱ] = [ℰ] · [ℱ]` in `K₀(Vect(X))`. -/
theorem classOf_tensorSymOne (E F : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    classOf X (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj
        ((SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) F).symmetric.piece
          ((1 : ℕ) : ℤ))) = classOf X E * classOf X F :=
  (classOf_eq_of_iso (tensorSymOneIso E F) (isFiniteLocallyFree_tensorSymOne E F hE hF)).trans
    (classOf_mul E F hE hF).symm

/-- For an epimorphism `p : M ⟶ N` of finite locally free modules, `[M] = [ker p] + [N]`. -/
private theorem classOf_eq_kernel_add_of_epi {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    classOf X M = classOf X (kernel p) + classOf X N :=
  classOf_shortExact (kernel.ι p) p (kernel.condition p) (isFiniteLocallyFree_kernel p hM hN) hM hN
    (ShortComplex.exact_kernel p)

/-- **The filtration relation of Tag 0FEJ for `Sym²`.** Along a short exact sequence
`0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules on a scheme,
`[Sym² ℱ] = [Sym² ℰ] + [ℰ ⊗ 𝒢] + [Sym² 𝒢]` in `K₀(Vect(X))`. -/
theorem classOf_sym_shortExact_of_isFiniteLocallyFree {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    classOf X (secondSymmetricPower X F) =
      classOf X (secondSymmetricPower X E) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
          classOf X (secondSymmetricPower X G) := by
  let J := Opens.grothendieckTopology (X : TopCat)
  have : Mono (C := SheafOfModules.{u} (Sheaf.toRingCat J X.sheaf)) f := hmono
  have : Epi (C := SheafOfModules.{u} (Sheaf.toRingCat J X.sheaf)) g := hepi
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat J X.sheaf) G := isFiniteLocallyFree_toSheaf hG
  let AE := SheafOfModules.algebras J E
  let AF := SheafOfModules.algebras J F
  let AG := SheafOfModules.algebras J G
  let S := SheafOfModules.SymPresentation.symComplex AF.symmetricGenerator AG.symmetricGenerator
    AF.symmetric_isSymmetricAlgebra AG.symmetric_isSymmetricAlgebra f g w 1
  obtain ⟨hSex, hSepi⟩ := SheafOfModules.SymPresentation.symmetricPresentation_exact
    AF.symmetricGenerator AG.symmetricGenerator AF.symmetric_isSymmetricAlgebra
    AG.symmetric_isSymmetricAlgebra f g w hex 1
  have hSymE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (AE.symmetric.piece ((1 + 1 : ℕ) : ℤ)) := isFiniteLocallyFree_secondSymmetricPower E hE
  have hSymF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂ :=
    isFiniteLocallyFree_secondSymmetricPower F hF
  have hSymG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃ :=
    isFiniteLocallyFree_secondSymmetricPower G hG
  have hX₁ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁ :=
    isFiniteLocallyFree_tensorSymOne E F hE hF
  have hK := @isFiniteLocallyFree_kernel X _ _ S.g hSepi hSymF hSymG
  have h1 : classOf X S.X₂ = classOf X (kernel S.g) + classOf X S.X₃ :=
    @classOf_eq_kernel_add_of_epi X _ _ S.g hSepi hSymF hSymG
  let b := kernel.lift S.g S.f S.zero
  have hb : Epi b := (ShortComplex.exact_iff_epi_kernel_lift S).1 hSex
  have h2 : classOf X S.X₁ = classOf X (kernel b) + classOf X (kernel S.g) :=
    @classOf_eq_kernel_add_of_epi X _ _ b hb hX₁ hK
  let mE := SheafOfModules.SymSquareFiltration.mulE AE.symmetricGenerator AG.symmetricGenerator
    AE.symmetric_isSymmetricAlgebra AG.symmetric_isSymmetricAlgebra f g w 1
  have hmE : Epi mE := SheafOfModules.SymSquareFiltration.epi_mulE AE.symmetricGenerator
    AG.symmetricGenerator AE.symmetric_isSymmetricAlgebra AG.symmetric_isSymmetricAlgebra f g w 1
  have hX₁E : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj
        (AE.symmetric.piece ((1 : ℕ) : ℤ))) := isFiniteLocallyFree_tensorSymOne E E hE hE
  have hKE := @isFiniteLocallyFree_kernel X _ _ mE hmE hX₁E hSymE
  have h3 : classOf X (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj
        (AE.symmetric.piece ((1 : ℕ) : ℤ))) =
      classOf X (kernel mE) + classOf X (AE.symmetric.piece ((1 + 1 : ℕ) : ℤ)) :=
    @classOf_eq_kernel_add_of_epi X _ _ mE hmE hX₁E hSymE
  have e : kernel mE ≅ kernel b :=
    SheafOfModules.SymSquareFiltration.kernelMulIso AE.symmetricGenerator AF.symmetricGenerator
        AG.symmetricGenerator AE.symmetric_isSymmetricAlgebra AF.symmetric_isSymmetricAlgebra
        AG.symmetric_isSymmetricAlgebra f g w 1 hex rfl ≪≫
      kernelIsoOfEq (kernel.lift_ι S.g S.f S.zero).symm ≪≫ kernelCompMono b (kernel.ι S.g)
  have h4 : classOf X (kernel mE) = classOf X (kernel b) := classOf_eq_of_iso e hKE
  have h5 : classOf X S.X₁ = classOf X E * classOf X F := classOf_tensorSymOne E F hE hF
  have h6 := classOf_tensorSymOne E E hE hE
  have h7 : classOf X F = classOf X E + classOf X G := classOf_shortExact f g w hE hF hG hex
  have h8 : classOf X E * classOf X G =
      classOf X (Scheme.Modules.tensorObjRingedSpace X E G) := classOf_mul E G hE hG
  show classOf X S.X₂ = classOf X (AE.symmetric.piece ((1 + 1 : ℕ) : ℤ)) +
    classOf X (Scheme.Modules.tensorObjRingedSpace X E G) + classOf X S.X₃
  linear_combination h1 - h2 + h5 - h6 + h3 + h4 + classOf X E * h7 + h8

/-- **The filtration relation of Tag 0FEJ for `⋀²`**:
`[⋀² ℱ] = [⋀² ℰ] + [ℰ ⊗ 𝒢] + [⋀² 𝒢]`, from the one for `Sym²` and
`[⋀² ℳ] + [Sym² ℳ] = [ℳ]²`. -/
theorem classOf_alt_shortExact_of_isFiniteLocallyFree {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    classOf X (secondExteriorPower X F) =
      classOf X (secondExteriorPower X E) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
          classOf X (secondExteriorPower X G) :=
  classOf_alt_shortExact_of_sym isFiniteLocallyFree_secondSymmetricPower
    isFiniteLocallyFree_secondExteriorPower f g w hE hF hG hmono hepi hex
    (classOf_sym_shortExact_of_isFiniteLocallyFree f g w hE hF hG hmono hepi hex)

/-- **`SquarePowersData` from the symmetric product relation.** If
`[Sym²(ℰ ⊗ ℱ)] = [⋀²ℰ ⊗ ⋀²ℱ] + [Sym²ℰ ⊗ Sym²ℱ]` in `K₀(Vect(X))` for all finite locally free
`ℰ` and `ℱ`, then `SquarePowersData X` holds. -/
theorem SquarePowersData.of_classOf_sym_tensor
    (hsym : ∀ E F : X.Modules,
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
          classOf X (secondSymmetricPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
            classOf X (Scheme.Modules.tensorObjRingedSpace X
                (secondExteriorPower X E) (secondExteriorPower X F)) +
              classOf X (Scheme.Modules.tensorObjRingedSpace X
                (secondSymmetricPower X E) (secondSymmetricPower X F))) :
    SquarePowersData X where
  isFiniteLocallyFree_sym := isFiniteLocallyFree_secondSymmetricPower
  isFiniteLocallyFree_alt := isFiniteLocallyFree_secondExteriorPower
  classOf_sym_shortExact f g w hE hF hG hmono hepi hex :=
    classOf_sym_shortExact_of_isFiniteLocallyFree f g w hE hF hG hmono hepi hex
  classOf_alt_shortExact f g w hE hF hG hmono hepi hex :=
    classOf_alt_shortExact_of_isFiniteLocallyFree f g w hE hF hG hmono hepi hex
  classOf_sym_tensor E F hE hF := hsym E F hE hF
  classOf_alt_tensor E F hE hF :=
    classOf_alt_tensor_of_sym isFiniteLocallyFree_secondSymmetricPower
      isFiniteLocallyFree_secondExteriorPower E F hE hF (hsym E F hE hF)

end AlgebraicGeometry.VectorBundleKZero

end
