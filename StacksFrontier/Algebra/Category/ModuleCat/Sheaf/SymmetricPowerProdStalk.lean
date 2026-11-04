module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf
public import StacksFrontier.LinearAlgebra.SymmetricPower.Prod

/-!
# The symmetric power of a direct sum of sheaves of modules, at a stalk

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, and `F`, `G`, `H`
sheaves of `O♯`-modules with chosen symmetric algebras. If the stalk of `H` at `x` splits as
`F_x × G_x` — as it does when `H` is a biproduct of `F` and `G`, and more generally for any
splitting datum `F ⇄ H ⇄ G` — then the stalk at `x` of the degree-`n` symmetric power of `H` is

`⨁_{p + q = n} (Symᵖ F)_x ⊗_{O_x} (Sym^q G)_x`.

This is the symmetric counterpart of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdStalk`, and it is the same
composite: the stalk comparison of Stacks Tag 01CH in degree `n`, transport along the splitting,
the algebraic Künneth decomposition `SymPow.prodEquivDirectSum`, and the degreewise stalk
comparisons for the two summands read backwards.

## Main definitions

* `SheafOfModules.symmetricPowerStalkEquivDirectSumOfStalkSplit`: the decomposition for a given
  linear equivalence `H_x ≅ F_x × G_x`.
* `SheafOfModules.symmetricPowerStalkEquivDirectSumOfSplit`: the decomposition for a splitting
  datum `F ⇄ H ⇄ G` of sheaves of modules.
* `SheafOfModules.symmetricPowerBiprodStalkEquivDirectSum`: **the decomposition for a binary
  biproduct**, `(Symⁿ (F ⊞ G))_x ≅ ⨁_{p + q = n} (Symᵖ F)_x ⊗ (Sym^q G)_x`.

## Implementation notes

The splitting of a stalk is `SheafOfModules.stalkProdEquivOfSplit`, and its biproduct instance
`SheafOfModules.biprodStalkProdEquiv`; both are proved in the exterior file and are statements
about the sheaves alone, with no exterior algebra in them, so they are reused verbatim.

The index set is the subtype `{pq : ℕ × ℕ // pq.1 + pq.2 = n}`, as in the algebraic
decomposition. Promoting this stalkwise statement to an isomorphism of sheaves of modules needs,
in addition, the comparison morphism out of the direct sum and the computation of its stalk map;
that is the symmetric counterpart of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf` and is not done here.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace
open scoped DirectSum TensorProduct

universe u

namespace SheafOfModules

section Split

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **The Künneth decomposition of a symmetric power at a stalk, for a splitting of the stalk.**
Given symmetric algebras of `F`, `G` and `H` and a linear equivalence `H_x ≅ F_x × G_x`, the
stalk at `x` of the degree-`n` symmetric power of `H` is
`⨁_{p + q = n} (Symᵖ F)_x ⊗ (Sym^q G)_x`.

The composite is: the stalk of `Symⁿ H` is `Symⁿ (H_x)` (Tag 01CH in degree `n`), transported
along the splitting to `Symⁿ (F_x × G_x)`, decomposed by `SymPow.prodEquivDirectSum`, and read
back degreewise through the stalk comparisons for `F` and `G`. -/
noncomputable def symmetricPowerStalkEquivDirectSumOfStalkSplit (n : ℕ) (x : ↥X)
    (e : ↑(TopCat.Presheaf.stalk H.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) ×
          ↑(TopCat.Presheaf.stalk G.val.presheaf x))) :
    ↑(TopCat.Presheaf.stalk (A.symmetricPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.symmetricPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.symmetricPower pq.1.2).val.presheaf x)) :=
  A.symmetricPowerStalkEquiv n x ≪≫ₗ SymPow.symmetricPowerCongr n e ≪≫ₗ
    SymPow.prodEquivDirectSum n ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
      TensorProduct.congr (AF.symmetricPowerStalkEquiv pq.1.1 x).symm
        (AG.symmetricPowerStalkEquiv pq.1.2 x).symm)

/-- **The Künneth decomposition of a symmetric power at a stalk, for a split sheaf of modules.**
If `F ⇄ H ⇄ G` is a splitting datum then the stalk at `x` of the degree-`n` symmetric power of
`H` is `⨁_{p + q = n} (Symᵖ F)_x ⊗ (Sym^q G)_x`. -/
noncomputable def symmetricPowerStalkEquivDirectSumOfSplit (n : ℕ) (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G)
    (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H) :
    ↑(TopCat.Presheaf.stalk (A.symmetricPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.symmetricPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.symmetricPower pq.1.2).val.presheaf x)) :=
  symmetricPowerStalkEquivDirectSumOfStalkSplit AF AG A n x
    (stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot)

end Split

section Biprod

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The Künneth decomposition of a symmetric power of a biproduct, at a stalk.** For sheaves of
modules `F` and `G` on `X` with chosen symmetric algebras, and a symmetric algebra of their
biproduct, the stalk at `x` of `Symⁿ (F ⊞ G)` is
`⨁_{p + q = n} (Symᵖ F)_x ⊗_{O_x} (Sym^q G)_x`. -/
noncomputable def symmetricPowerBiprodStalkEquivDirectSum [HasBinaryBiproduct F G]
    (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
    (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) (F ⊞ G))
    (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.symmetricPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.symmetricPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.symmetricPower pq.1.2).val.presheaf x)) :=
  symmetricPowerStalkEquivDirectSumOfStalkSplit AF AG A n x (biprodStalkProdEquiv F G x)

end Biprod

end SheafOfModules

end
