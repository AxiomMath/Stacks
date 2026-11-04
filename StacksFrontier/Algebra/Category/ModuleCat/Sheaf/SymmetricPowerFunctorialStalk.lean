module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf
public import StacksFrontier.LinearAlgebra.SymmetricPower.Prod

/-!
# The stalk of the induced map on symmetric powers, and monomorphy

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `M`, `N` sheaves of
`O♯`-modules with chosen symmetric algebras, and `f : M ⟶ N` a morphism. The induced map
`Symⁿ f : Symⁿ M ⟶ Symⁿ N` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial` is built from the
universal property, so nothing about it is sectionwise. **This file identifies its stalk map**:
read through the comparisons of Stacks Tag 01CH on source and target, the stalk at `x` of
`Symⁿ f` is `Symⁿ` of the stalk map `f_x` of `f`.

Monomorphy of `Symⁿ f` then becomes a question about one module map at a time. `Symⁿ` of a
linear map with a left inverse is injective, by functoriality and nothing else
(`SymPow.symMap_injective_of_leftInverse`), so `Symⁿ f` is a monomorphism as soon as every stalk
map of `f` admits a left inverse. That hypothesis is the stalkwise form of "`f` is locally a
split injection": for the inclusion of a subsheaf whose quotient has free stalks the stalk
sequence is a short exact sequence with projective third term, so the inclusion of stalks splits.
Nothing below derives the hypothesis from local freeness — the stalkwise statement is what the
results take as input, and deducing it from a short exact sequence of finite locally free sheaves
is a separate step.

## Main definitions

* `SheafOfModules.germProdSet`: the germs at `x` of the local sections `s₀ ⋯ sₙ₋₁` of `Symⁿ M`,
  each written with the data of the symmetric algebra alone as the ordered product of the images
  of the `sᵢ` under its degree-one generator.

## Main results

* `SheafOfModules.span_germProdSet_eq_top`: germs of products of local sections span the stalk of
  a symmetric power. This is what makes the stalk of a map out of `Symⁿ M` determined by its
  values on such germs.
* `SheafOfModules.symmetricPowerStalkEquiv_stalkMapL_pieceMap`: **the stalk of `Symⁿ f` is
  `Symⁿ` of the stalk of `f`**, read through the comparisons of Tag 01CH.
* `SheafOfModules.injective_stalkMapL_pieceMap_of_leftInverse` and
  `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.mono_pieceMap_of_stalkwise_leftInverse`:
  **`Symⁿ f` is a monomorphism when every stalk map of `f` has a left inverse.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.mono_symmetricSquareMap_of_stalkwise_leftInverse`:
  the degree-two case, **`Sym²E ⟶ Sym²F` is a monomorphism**, for a package of the three
  algebras.

## Implementation notes

The identification is proved on a spanning set and nowhere else. Both sides are
`↑(O_x)`-linear maps out of the stalk of `Symⁿ M`; germs of products of local sections span that
stalk, because products of degree-one generators span `Symⁿ` of a module
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`) and a finite family of germs is a family of
germs of sections over one common neighbourhood. On such a germ the computation is the
degree-`n` component of the characterizing equation `IsSymmetricAlgebra.map_app_one`, in the form
`SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp`.

The spanning statement is phrased through the image of the span under the comparison rather than
inside the subtype `↥(Symⁿ (M_x))`: it is the submodule `Submodule.map` of the span along the
comparison followed by the inclusion of the symmetric power into the symmetric algebra, so the
span induction runs in `Sym(M_x)` where `symmetricPower_eq_span_prod_ι` lives.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A B : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (gen : M ⟶ A.piece 1) (gen' : N ⟶ B.piece 1)
  (hA : GradedAlgebra.IsSymmetricAlgebra A gen)
  (hB : GradedAlgebra.IsSymmetricAlgebra B gen')

/-! ### Germs of products of local sections span -/

/-- The germs at `x` of the local sections `s₀ ⋯ sₙ₋₁` of `Symⁿ M`, as a subset of the stalk of
`Symⁿ M`; each product is written with the data of the symmetric algebra alone, as the ordered
product of the images of the `sᵢ` under its degree-one generator. -/
def germProdSet (n : ℕ) (x : ↥X) :
    Set ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x) :=
  {z | ∃ (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
    z = TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
      (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
        fun i => gen.val.app (op U) (s i))}

/-- Every product of germs is the germ of a product of local sections: a finite family of germs
is a family of germs of sections over one common neighbourhood, and the comparison of Tag 01CH in
degree `n` carries the germ of the product of those sections to the product of the germs. -/
theorem symm_prod_ι_mem_germProdSet (n : ℕ) (x : ↥X)
    (v : Fin n → ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    (symmetricPowerStalkEquiv A gen hA n x).symm
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x) (v i),
          SymmetricAlgebra.prod_ι_mem ↑(TopCat.Presheaf.stalk Osharp.obj x) v⟩ ∈
      germProdSet gen n x := by
  choose U hU s hs using fun i : Fin n => TopCat.Presheaf.exists_germ_eq M.val.presheaf (v i)
  have hW : x ∈ (⨅ i, U i : Opens ↥X) := by
    have h : x ∈ (↑(⨅ i, U i) : Set ↥X) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    exact h
  refine ⟨(⨅ i, U i : Opens ↥X), hW, fun i => M.val.map (homOfLE (iInf_le U i)).op (s i), ?_⟩
  refine (LinearEquiv.symm_apply_eq (symmetricPowerStalkEquiv A gen hA n x)).2 (Subtype.ext ?_)
  refine Eq.trans ?_ (symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA n x
    (⨅ i, U i : Opens ↥X) hW (fun i => M.val.map (homOfLE (iInf_le U i)).op (s i))).symm
  exact congrArg (fun w : Fin n → ↑(TopCat.Presheaf.stalk M.val.presheaf x) =>
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) (w i))
    (funext fun i => ((TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE (iInf_le U i)) x hW (s i)).trans (hs i)).symm)

include hA in
/-- **Germs of products of local sections span the stalk of a symmetric power.** The stalk of
`Symⁿ M` at `x` is `Symⁿ (M_x)` (Tag 01CH in degree `n`), in which the products of degree-one
generators span (`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), and every such product is the
image of a germ of a product of local sections
(`SheafOfModules.symm_prod_ι_mem_germProdSet`). -/
theorem span_germProdSet_eq_top (n : ℕ) (x : ↥X) :
    Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x) (germProdSet gen n x) = ⊤ := by
  have hle : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        (Set.range fun v : Fin n → ↑(TopCat.Presheaf.stalk M.val.presheaf x) =>
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x) (v i)) ≤
      Submodule.map ((SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)).subtype.comp
          (symmetricPowerStalkEquiv A gen hA n x).toLinearMap)
        (Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x) (germProdSet gen n x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine ⟨(symmetricPowerStalkEquiv A gen hA n x).symm
      ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x) (v i),
        SymmetricAlgebra.prod_ι_mem ↑(TopCat.Presheaf.stalk Osharp.obj x) v⟩,
      Submodule.subset_span (symm_prod_ι_mem_germProdSet gen hA n x v),
      congrArg Subtype.val ((symmetricPowerStalkEquiv A gen hA n x).apply_symm_apply _)⟩
  refine eq_top_iff.2 fun z _ => ?_
  have hmem : ((symmetricPowerStalkEquiv A gen hA n x z) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x)) ∈
      Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        (Set.range fun v : Fin n → ↑(TopCat.Presheaf.stalk M.val.presheaf x) =>
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x) (v i)) := by
    rw [← SymmetricAlgebra.symmetricPower_eq_span_prod_ι
      ↑(TopCat.Presheaf.stalk Osharp.obj x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) n]
    exact (symmetricPowerStalkEquiv A gen hA n x z).2
  obtain ⟨t, htS, ht⟩ := hle hmem
  have hz : t = z := by
    refine (symmetricPowerStalkEquiv A gen hA n x).injective (Subtype.ext ?_)
    exact ht
  rwa [hz] at htS

/-! ### The stalk of the induced map -/

/-- **The stalk of `Symⁿ f` is `Symⁿ` of the stalk of `f`**, read through the comparisons of
Tag 01CH on the source and the target.

Both sides are linear maps out of the stalk of `Symⁿ M`, and germs of products of local sections
span it (`SheafOfModules.span_germProdSet_eq_top`), so the value on such a germ determines the
identification; there it is the degree-`n` component of the equation
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.map_app_one` characterizing `Symⁿ f`. -/
theorem symmetricPowerStalkEquiv_stalkMapL_pieceMap (f : M ⟶ N) (n : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)) :
    symmetricPowerStalkEquiv B gen' hB n x
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (n : ℤ)).val z) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x f.val)
        (symmetricPowerStalkEquiv A gen hA n x z) := by
  have hkey : ∀ ξ ∈ germProdSet gen n x,
      ((symmetricPowerStalkEquiv B gen' hB n x).toLinearMap.comp
          (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (n : ℤ)).val)) ξ =
        ((SymPow.symMap n (PresheafOfModules.stalkMapL x f.val)).comp
          (symmetricPowerStalkEquiv A gen hA n x).toLinearMap) ξ := by
    rintro ξ ⟨U, hx, s, rfl⟩
    refine Subtype.ext ?_
    have hstalk := PresheafOfModules.stalkMapL_germ x (hA.pieceMap hB f (n : ℤ)).val U hx
      (A.toPresheafGradedAlgebra.homogeneousProd (op U) n fun i => gen.val.app (op U) (s i))
    have happ := GradedAlgebra.UnitalHom.app_homogeneousProd_comp
      (hA.map hB f) f (hA.map_app_one hB f) (op U) n s
    have hleft : ((symmetricPowerStalkEquiv B gen' hB n x
          (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (n : ℤ)).val
            (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
              (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
                fun i => gen.val.app (op U) (s i))))) :
            SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk N.val.presheaf x)) =
        ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk N.val.presheaf x)
          (TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) (s i))) := by
      refine Eq.trans (congrArg (fun y => (symmetricPowerStalkEquiv B gen' hB n x y :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk N.val.presheaf x))) (hstalk.trans (congrArg
            (TopCat.Presheaf.germ (B.piece (n : ℤ)).val.presheaf U x hx) happ))) ?_
      exact symmetricPowerStalkEquiv_germ_homogeneousProd B gen' hB n x U hx
        fun i => f.val.app (op U) (s i)
    have hright : ((SymPow.symMap n (PresheafOfModules.stalkMapL x f.val)
            (symmetricPowerStalkEquiv A gen hA n x
              (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
                (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
                  fun i => gen.val.app (op U) (s i))))) :
            SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk N.val.presheaf x)) =
        ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk N.val.presheaf x)
          (TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) (s i))) := by
      refine Eq.trans (SymPow.symMap_coe n (PresheafOfModules.stalkMapL x f.val) _) ?_
      refine Eq.trans (congrArg (SymPow.symAlgMap (PresheafOfModules.stalkMapL x f.val))
        (symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA n x U hx s)) ?_
      refine Eq.trans (SymPow.symAlgMap_prod_ι (PresheafOfModules.stalkMapL x f.val) n
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) ?_
      exact congrArg (fun w : Fin n → ↑(TopCat.Presheaf.stalk N.val.presheaf x) =>
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk N.val.presheaf x) (w i))
        (funext fun i => PresheafOfModules.stalkMapL_germ x f.val U hx (s i))
    exact hleft.trans hright.symm
  exact LinearMap.congr_fun
    (LinearMap.ext_on (span_germProdSet_eq_top gen hA n x) hkey) z

/-- **The stalk map of `Symⁿ f` is injective** when the stalk map of `f` at that point has a left
inverse — as it has when `f` is locally a split injection. Under the comparisons of Tag 01CH the
stalk map is `Symⁿ` of the stalk map of `f`
(`SheafOfModules.symmetricPowerStalkEquiv_stalkMapL_pieceMap`), and `Symⁿ` of a linear map with a
left inverse is split injective (`SymPow.symMap_injective_of_leftInverse`). -/
theorem injective_stalkMapL_pieceMap_of_leftInverse (f : M ⟶ N) (n : ℕ) (x : ↥X)
    (g : ↑(TopCat.Presheaf.stalk N.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x))
    (hg : g.comp (PresheafOfModules.stalkMapL x f.val) = LinearMap.id) :
    Function.Injective
      (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (n : ℤ)).val) := by
  intro z z' hzz'
  refine (symmetricPowerStalkEquiv A gen hA n x).injective
    (SymPow.symMap_injective_of_leftInverse n (PresheafOfModules.stalkMapL x f.val) g hg ?_)
  refine (symmetricPowerStalkEquiv_stalkMapL_pieceMap gen gen' hA hB f n x z).symm.trans ?_
  refine Eq.trans ?_ (symmetricPowerStalkEquiv_stalkMapL_pieceMap gen gen' hA hB f n x z')
  exact congrArg (symmetricPowerStalkEquiv B gen' hB n x) hzz'

namespace GradedAlgebra.IsSymmetricAlgebra

/-- **`Symⁿ f` is a monomorphism as soon as every stalk map of `f` admits a left inverse.**

Monomorphy of a morphism of sheaves of modules on a space is injectivity of its stalk maps
(Stacks Tag 01AG, `AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap`), and the stalk
map is injective by `SheafOfModules.injective_stalkMapL_pieceMap_of_leftInverse`.

The hypothesis is the stalkwise form of "`f` is locally a split injection": for the inclusion of
a subsheaf whose quotient has free stalks the stalk sequence is a short exact sequence with
projective third term, so the inclusion of stalks splits. -/
theorem mono_pieceMap_of_stalkwise_leftInverse (f : M ⟶ N) (n : ℕ)
    (hsplit : ∀ x : ↥X, ∃ g : ↑(TopCat.Presheaf.stalk N.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk
        Osharp.obj x)] ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      g.comp (PresheafOfModules.stalkMapL x f.val) = LinearMap.id) :
    Mono (hA.pieceMap hB f (n : ℤ)) := by
  rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro x a b hab
  obtain ⟨g, hg⟩ := hsplit x
  refine injective_stalkMapL_pieceMap_of_leftInverse gen gen' hA hB f n x g hg ?_
  exact (stalkMap_hom_eq_stalkMapL x (hA.pieceMap hB f (n : ℤ)) a).symm.trans
    (hab.trans (stalkMap_hom_eq_stalkMapL x (hA.pieceMap hB f (n : ℤ)) b))

end GradedAlgebra.IsSymmetricAlgebra

/-! ### The degree-two case for a package of the three algebras -/

namespace TensorExteriorSymmetricAlgebras

variable {G G' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **`Sym²E ⟶ Sym²F` is a monomorphism** when every stalk map of `E ⟶ F` admits a left inverse,
for the symmetric algebras carried by two `TensorExteriorSymmetricAlgebras` packages. This is the
clause the two-step filtration of `Sym²F` with sub `Sym²E` and graded quotients `E ⊗ G`,
`Sym²G` rests on. -/
theorem mono_symmetricSquareMap_of_stalkwise_leftInverse
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
    (A' : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G') (f : G ⟶ G')
    (hsplit : ∀ x : ↥X, ∃ g : ↑(TopCat.Presheaf.stalk G'.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk
        Osharp.obj x)] ↑(TopCat.Presheaf.stalk G.val.presheaf x),
      g.comp (PresheafOfModules.stalkMapL x f.val) = LinearMap.id) :
    Mono (A.symmetricSquareMap A' f) :=
  GradedAlgebra.IsSymmetricAlgebra.mono_pieceMap_of_stalkwise_leftInverse A.symmetricGenerator
    A'.symmetricGenerator A.symmetric_isSymmetricAlgebra A'.symmetric_isSymmetricAlgebra f 2
    hsplit

end TensorExteriorSymmetricAlgebras

end SheafOfModules

end
