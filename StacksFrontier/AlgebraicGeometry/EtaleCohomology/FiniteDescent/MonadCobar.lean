module

public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# The cobar resolution of a monad, and its contraction after applying the left adjoint

Let `L : A ⥤ B` and `R : B ⥤ A` be adjoint functors, `adj : L ⊣ R`, and let `T = L ⋙ R` be the
induced monad on `A`. The cobar, or Godement, construction attaches to an object `X : A` the
augmented cosimplicial object
`X ⟶ T X ⟶ T² X ⟶ ⋯`,
whose cofaces insert the unit `η : 𝟭 A ⟶ T` into each of the available slots and whose
codegeneracies contract two adjacent slots using the multiplication `μ : T ⋙ T ⟶ T`.

Since `StacksFrontier.AlgebraicTopology.StandardResolution.Godement` builds Godement's system for a
*comonad* and produces a *simplicial* object, everything here is carried out in `Aᵒᵖ`, where
`T.op` is a comonad with counit `cod adj = NatTrans.op adj.unit` and comultiplication
`cos adj = NatTrans.op μ`. The three comonad identities are the three monad identities of
`T = L ⋙ R` read backwards, and they reduce to the two triangle identities of the adjunction and
naturality of its counit.

Applying `L` to the cobar resolution makes it contractible. The reason is that
`L (T^{n+1} X) = L (R (L (⋯)))` is, by strict associativity of `⋙` in Lean, the value at `L X` of
the `(n+1)`-st power of the comonad `S = R ⋙ L` of the adjunction on `B`; no comparison
isomorphism is needed anywhere. The counit `ε_{LW} : L (R (L W)) ⟶ L W`, applied at the outermost
slot, is then an extra degeneracy in the sense of
`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`: the triangle identity
`L(η_W) ≫ ε_{LW} = 1` makes the zeroth face cancel it, and naturality of `ε` makes it commute with
the augmentation, with the remaining faces and with the degeneracies. Mathlib's
`ExtraDegeneracy.homotopyEquiv` then exhibits the augmentation of the alternating face map complex
of the `L`-image as a homotopy equivalence, hence a quasi-isomorphism: the `L`-image of the
augmented cobar complex of `X` is contractible.

## Main definitions

* `Stacks.Cobar.mnd`: the monad `T = L ⋙ R` of the adjunction, as a bare endofunctor of `A`.
* `Stacks.Cobar.cod`, `Stacks.Cobar.cos`: the counit `T.op ⟶ 𝟭 Aᵒᵖ` and comultiplication
  `T.op ⟶ T.op ⋙ T.op` of the comonad on `Aᵒᵖ` opposite to `T`.
* `Stacks.Cobar.cosplit`: the transformation `L.op ⟶ T.op ⋙ L.op` given by the counit of the
  adjunction at `L`, which is the extra degeneracy.
* `Stacks.Cobar.extraDegeneracy`: the extra degeneracy carried by the `L.op`-image of the cobar
  resolution.

## Main results

* `Stacks.Cobar.cos_comp_whiskerLeft_cod`, `Stacks.Cobar.cos_comp_whiskerRight_cod`,
  `Stacks.Cobar.cos_coassoc`: `(T.op, cod adj, cos adj)` is a comonad on `Aᵒᵖ`, in exactly the
  shape that `CategoryTheory.Godement.exists_augmented_standardResolution_whisker` asks for.
* `Stacks.Cobar.exists_augmented_cobar`: the cobar resolution of `X : A` exists as an augmented
  simplicial object of `Aᵒᵖ` with degree-`n` term `op (T^{n+1} X)`, augmentation point `op X`,
  faces `Godement.face (cod adj)`, degeneracies `Godement.degeneracy (cos adj)` and augmentation
  `cod adj`, all evaluated at `op X`.
* `Stacks.Cobar.exists_homotopyEquiv_alternatingFaceMapComplex`: the alternating face map complex
  of the `L.op`-image of the cobar resolution is homotopy equivalent to `op (L X)` placed in
  degree `0`.

## References

* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
* [Stacks Project, Tag 0G5N](https://stacks.math.columbia.edu/tag/0G5N)
* [Stacks Project, Tag 0G5P](https://stacks.math.columbia.edu/tag/0G5P)
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe v₁ v₂ u₁ u₂

namespace Stacks.Cobar

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {L : A ⥤ B} {R : B ⥤ A}

/-- The monad of an adjunction `L ⊣ R`, as a bare endofunctor `T = L ⋙ R` of `A`. -/
public abbrev mnd (L : A ⥤ B) (R : B ⥤ A) : A ⥤ A := L ⋙ R

variable (adj : L ⊣ R)

/-- The counit `T.op ⟶ 𝟭 Aᵒᵖ` of the comonad on `Aᵒᵖ` opposite to the monad `T = L ⋙ R`: it is
the unit `η : 𝟭 A ⟶ T` of the adjunction, read in the opposite category. -/
public def cod : (mnd L R).op ⟶ 𝟭 Aᵒᵖ := NatTrans.op adj.unit

/-- The comultiplication `T.op ⟶ T.op ⋙ T.op` of the comonad on `Aᵒᵖ` opposite to the monad
`T = L ⋙ R`: it is the multiplication `μ = 1_R ⋆ ε ⋆ 1_L : T ⋙ T ⟶ T` of the adjunction, read in
the opposite category. -/
public def cos : (mnd L R).op ⟶ (mnd L R).op ⋙ (mnd L R).op :=
  NatTrans.op (Functor.whiskerRight (Functor.whiskerLeft L adj.counit) R)

/-- The left unit law `η_{TZ} ≫ μ_Z = 1` of the monad `T = L ⋙ R`, which is the triangle identity
`η_{RY} ≫ R(ε_Y) = 1` at `Y = L Z`. -/
private theorem unit_comp_mu (Z : A) :
    adj.unit.app (R.obj (L.obj Z)) ≫ R.map (adj.counit.app (L.obj Z)) = 𝟙 (R.obj (L.obj Z)) :=
  adj.right_triangle_components (L.obj Z)

/-- The right unit law `T(η_Z) ≫ μ_Z = 1` of the monad `T = L ⋙ R`, which is the `R`-image of the
triangle identity `L(η_Z) ≫ ε_{LZ} = 1`. -/
private theorem map_unit_comp_mu (Z : A) :
    R.map (L.map (adj.unit.app Z)) ≫ R.map (adj.counit.app (L.obj Z)) = 𝟙 (R.obj (L.obj Z)) := by
  rw [← R.map_comp]
  simp

/-- Associativity `μ_{TZ} ≫ μ_Z = T(μ_Z) ≫ μ_Z` of the monad `T = L ⋙ R`, which is the `R`-image
of naturality of the counit at `ε_{LZ}`. -/
private theorem mu_comp_mu (Z : A) :
    R.map (adj.counit.app (L.obj (R.obj (L.obj Z)))) ≫ R.map (adj.counit.app (L.obj Z))
      = R.map (L.map (R.map (adj.counit.app (L.obj Z)))) ≫ R.map (adj.counit.app (L.obj Z)) := by
  rw [← R.map_comp, ← R.map_comp]
  exact congrArg R.map (adj.counit.naturality (adj.counit.app (L.obj Z))).symm

/-- The first counit identity of the comonad `(T.op, cod adj, cos adj)` on `Aᵒᵖ`: it is the left
unit law `η_{TZ} ≫ μ_Z = 1` of the monad `T = L ⋙ R`, read in the opposite category. -/
public theorem cos_comp_whiskerLeft_cod :
    cos adj ≫ Functor.whiskerLeft (mnd L R).op (cod adj) = 𝟙 _ := by
  ext ⟨Z⟩
  exact congrArg Quiver.Hom.op (unit_comp_mu adj Z)

/-- The second counit identity of the comonad `(T.op, cod adj, cos adj)` on `Aᵒᵖ`: it is the right
unit law `T(η_Z) ≫ μ_Z = 1` of the monad `T = L ⋙ R`, read in the opposite category. -/
public theorem cos_comp_whiskerRight_cod :
    cos adj ≫ Functor.whiskerRight (cod adj) (mnd L R).op = 𝟙 _ := by
  ext ⟨Z⟩
  exact congrArg Quiver.Hom.op (map_unit_comp_mu adj Z)

/-- Coassociativity of the comonad `(T.op, cod adj, cos adj)` on `Aᵒᵖ`: it is associativity
`μ_{TZ} ≫ μ_Z = T(μ_Z) ≫ μ_Z` of the monad `T = L ⋙ R`, read in the opposite category. -/
public theorem cos_coassoc :
    cos adj ≫ Functor.whiskerLeft (mnd L R).op (cos adj)
      = cos adj ≫ Functor.whiskerRight (cos adj) (mnd L R).op := by
  ext ⟨Z⟩
  exact congrArg Quiver.Hom.op (mu_comp_mu adj Z)

/-! ### The splitting produced by the left adjoint -/

/-- The transformation `L.op ⟶ T.op ⋙ L.op` of functors `Aᵒᵖ ⥤ Bᵒᵖ` given at `op W` by the
counit component `ε_{LW} : L (R (L W)) ⟶ L W`, read in the opposite categories. It is the extra
degeneracy of the cobar resolution after the left adjoint has been applied: it inserts a new
*outermost* copy of the comonad `S = R ⋙ L` of `B`, which the zeroth coface cancels. -/
public def cosplit : L.op ⟶ (mnd L R).op ⋙ L.op :=
  NatTrans.op (Functor.whiskerLeft L adj.counit)

/-- The zeroth coface cancels the splitting: `L(η_W) ≫ ε_{LW} = 1`, the triangle identity, read
in the opposite categories. -/
public theorem cosplit_app_comp_map_cod_app (V : Aᵒᵖ) :
    (cosplit adj).app V ≫ L.op.map ((cod adj).app V) = 𝟙 (L.op.obj V) :=
  congrArg Quiver.Hom.op (adj.left_triangle_components V.unop)

/-- The splitting commutes past the image under `L.op` of any morphism of `Aᵒᵖ`: this is
naturality of `cosplit adj`, i.e. naturality of the counit of the adjunction. -/
public theorem cosplit_app_comp_map_op_map {V V' : Aᵒᵖ} (f : V ⟶ V') :
    (cosplit adj).app V ≫ L.op.map ((mnd L R).op.map f) = L.op.map f ≫ (cosplit adj).app V' :=
  ((cosplit adj).naturality f).symm

/-! ### The cobar resolution -/

/-- Opposites commute with iteration: the `n`-fold composite of `F.op` is the opposite of the
`n`-fold composite of `F`. -/
public theorem op_iterate {C : Type u₁} [Category.{v₁} C] (F : C ⥤ C) :
    ∀ n : ℕ, F.op.iterate n = (F.iterate n).op
  | 0 => rfl
  | n + 1 => congrArg (· ⋙ F.op) (op_iterate F n)

/-- On objects, the `n`-fold composite of `F.op` sends `op W` to the opposite of the `n`-fold
composite of `F` at `W`. -/
public theorem op_iterate_obj {C : Type u₁} [Category.{v₁} C] (F : C ⥤ C) (n : ℕ) (W : C) :
    (F.op.iterate n).obj (op W) = op ((F.iterate n).obj W) := by
  rw [op_iterate]
  rfl

/-- **The cobar resolution.**
Let `L ⊣ R` be an adjunction with monad `T = L ⋙ R` on `A` and let `X : A`. Read in `Aᵒᵖ`, the
cobar construction `X → T X → T² X → ⋯` is an augmented simplicial object `Z` of `Aᵒᵖ`: its
degree-`n` term is `op (T^{n+1} X)`, its augmentation point is `op X`, its faces are the
components at `op X` of Godement's faces `Godement.face (cod adj)`, its degeneracies those of
`Godement.degeneracy (cos adj)`, and its augmentation is the component at `op X` of the comonad
counit `cod adj`, i.e. the unit `η_X : X ⟶ T X` of the adjunction. -/
public theorem exists_augmented_cobar (X : A) :
    ∃ (Z : SimplicialObject.Augmented Aᵒᵖ)
      (h : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = ((mnd L R).op.iterate (n + 1)).obj (op X))
      (hZ : Z.right = op X),
      (∀ n : ℕ, Z.left.obj (op ⦋n⦌) = op (((mnd L R).iterate (n + 1)).obj X)) ∧
      (∀ (n : ℕ) (j : Fin (n + 2)),
        Z.left.δ j = eqToHom (h (n + 1)) ≫
          (Godement.face (cod adj) (n + 1) j).app (op X) ≫ eqToHom (h n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        Z.left.σ j = eqToHom (h n) ≫
          (Godement.degeneracy (cos adj) n j).app (op X) ≫ eqToHom (h (n + 1)).symm) ∧
      Z.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ (cod adj).app (op X) ≫ eqToHom hZ.symm := by
  obtain ⟨Y, hY, hYr, hδ, hσ, hhom⟩ :=
    Godement.exists_augmented_standardResolution_whisker (cod adj) (cos adj) (𝟭 Aᵒᵖ) (𝟭 Aᵒᵖ)
      (cos_comp_whiskerLeft_cod adj) (cos_comp_whiskerRight_cod adj) (cos_coassoc adj)
  set W : (Aᵒᵖ ⥤ Aᵒᵖ) ⥤ Aᵒᵖ := (evaluation Aᵒᵖ Aᵒᵖ).obj (op X) with hW
  set Z : SimplicialObject.Augmented Aᵒᵖ :=
    (SimplicialObject.Augmented.whiskeringObj _ _ W).obj Y with hZdef
  have h : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = ((mnd L R).op.iterate (n + 1)).obj (op X) :=
    fun n => congrArg W.obj (hY n)
  have hZ : Z.right = op X := congrArg W.obj hYr
  refine ⟨Z, h, hZ, fun n => (h n).trans (op_iterate_obj _ _ _), fun n j => ?_, fun n j => ?_, ?_⟩
  · exact Godement.Prep.map_eq_eqToHom_comp W (hδ n j)
  · exact Godement.Prep.map_eq_eqToHom_comp W (hσ n j)
  · exact (Category.comp_id _).trans (Godement.Prep.map_eq_eqToHom_comp W hhom)

/-! ### The extra degeneracy after applying the left adjoint -/

/-- The zeroth coface cancels the splitting, in the presence of a prefix and a suffix: if
`e ≫ g = 1`, then `e ≫ cosplit ≫ L.op(cod) ≫ g = 1`. -/
public theorem cosplit_comp_cod_comp {V : Aᵒᵖ} {U : Bᵒᵖ} (e : U ⟶ L.op.obj V)
    (g : L.op.obj V ⟶ U) (heg : e ≫ g = 𝟙 U) :
    e ≫ (cosplit adj).app V ≫ L.op.map ((cod adj).app V) ≫ g = 𝟙 U := by
  rw [← Category.assoc ((cosplit adj).app V), cosplit_app_comp_map_cod_app, Category.id_comp]
  exact heg

/-- Naturality of the splitting, in the presence of a prefix and a suffix. -/
public theorem cosplit_comp_op_map_comp {V V' : Aᵒᵖ} {U U' : Bᵒᵖ} (f : V ⟶ V')
    (e : U ⟶ L.op.obj V) (g : L.op.obj ((mnd L R).op.obj V') ⟶ U') :
    e ≫ (cosplit adj).app V ≫ L.op.map ((mnd L R).op.map f) ≫ g
      = e ≫ L.op.map f ≫ (cosplit adj).app V' ≫ g := by
  rw [← Category.assoc ((cosplit adj).app V), cosplit_app_comp_map_op_map, Category.assoc]

section Contraction

variable (X : A) (Z : SimplicialObject.Augmented Bᵒᵖ)
  (h : ∀ n : ℕ,
    Z.left.obj (op ⦋n⦌) = L.op.obj (((mnd L R).op.iterate (n + 1)).obj (op X)))
  (hZ : Z.right = L.op.obj (op X))

/-- **The contraction of the cobar resolution.**
Let `Z` be an augmented simplicial object of `Bᵒᵖ` which is the image under `L.op` of the cobar
resolution of `X : A`: its degree-`n` term is `op (L (T^{n+1} X))`, which by strict associativity
of `⋙` is `op (S^{n+1} (L X))` for the comonad `S = R ⋙ L` of the adjunction on `B`; its
augmentation point is `op (L X)`; and its faces, degeneracies and augmentation are the
`L.op`-images of Godement's. Then `Z` is contractible: the counit `ε_{L W} : L (R (L W)) ⟶ L W`
of the adjunction, applied at the outermost slot, is an extra degeneracy. The triangle identity
makes the zeroth face cancel it (`s'_comp_ε` and `s_comp_δ₀`), and naturality of the counit makes
it commute with the augmentation, with all the remaining faces and with the degeneracies
(`s₀_comp_δ₁`, `s_comp_δ` and `s_comp_σ`). -/
public def extraDegeneracy
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      Z.left.δ j = eqToHom (h (n + 1)) ≫
        L.op.map ((Godement.face (cod adj) (n + 1) j).app (op X)) ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)),
      Z.left.σ j = eqToHom (h n) ≫
        L.op.map ((Godement.degeneracy (cos adj) n j).app (op X)) ≫ eqToHom (h (n + 1)).symm)
    (hhom : Z.hom.app (op ⦋0⦌)
      = eqToHom (h 0) ≫ L.op.map ((cod adj).app (op X)) ≫ eqToHom hZ.symm) :
    SimplicialObject.Augmented.ExtraDegeneracy Z where
  s' := eqToHom hZ ≫ (cosplit adj).app (op X) ≫ eqToHom (h 0).symm
  s n := eqToHom (h n) ≫
    (cosplit adj).app (((mnd L R).op.iterate (n + 1)).obj (op X)) ≫ eqToHom (h (n + 1)).symm
  s'_comp_ε := by
    rw [hhom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact cosplit_comp_cod_comp adj _ _ (by simp)
  s₀_comp_δ₁ := by
    rw [hδ, hhom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact cosplit_comp_op_map_comp adj ((cod adj).app (op X)) _ _
  s_comp_δ₀ n := by
    rw [hδ, Godement.Prep.face_zero]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact cosplit_comp_cod_comp adj _ _ (by simp)
  s_comp_δ n i := by
    rw [hδ, hδ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact cosplit_comp_op_map_comp adj
      ((Godement.face (cod adj) (n + 1) i).app (op X)) _ _
  s_comp_σ n i := by
    rw [hσ, hσ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact cosplit_comp_op_map_comp adj
      ((Godement.degeneracy (cos adj) n i).app (op X)) _ _

end Contraction

/-! ### The augmented complex is contractible -/

include adj in
/-- **The conclusion.**
Let `L ⊣ R` be an adjunction between categories `A` and `B`, with `B` preadditive and with a zero
object, let `T = L ⋙ R` be the monad on `A`, and let `X : A`. Apply `L` to the cobar resolution
`X → T X → T² X → ⋯` of `X` and read the result in `Bᵒᵖ`: it is an augmented simplicial object
whose degree-`n` term is `op (L (T^{n+1} X))`. Its alternating face map complex is homotopy
equivalent, hence quasi-isomorphic, to `op (L X)` concentrated in degree `0`; in other words the
`L`-image of the augmented cobar complex of `X` is contractible. -/
public theorem exists_homotopyEquiv_alternatingFaceMapComplex
    [Preadditive B] [HasZeroObject B] (X : A) :
    ∃ Z : SimplicialObject.Augmented Aᵒᵖ,
      (∀ n : ℕ, Z.left.obj (op ⦋n⦌) = op (((mnd L R).iterate (n + 1)).obj X)) ∧
      Z.right = op X ∧
      Nonempty (HomotopyEquiv
        (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
          ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z)))
        ((ChainComplex.single₀ Bᵒᵖ).obj (op (L.obj X)))) := by
  obtain ⟨Z, h, hZ, hobj, hδ, hσ, hhom⟩ := exists_augmented_cobar adj X
  have h' : ∀ n : ℕ,
      ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z).left.obj (op ⦋n⦌)
        = L.op.obj (((mnd L R).op.iterate (n + 1)).obj (op X)) :=
    fun n => congrArg L.op.obj (h n)
  have hZ' : ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z).right
      = L.op.obj (op X) := congrArg L.op.obj hZ
  have ed := extraDegeneracy adj X _ h' hZ'
    (fun n j => Godement.Prep.map_eq_eqToHom_comp L.op (hδ n j))
    (fun n j => Godement.Prep.map_eq_eqToHom_comp L.op (hσ n j))
    ((Category.comp_id _).trans (Godement.Prep.map_eq_eqToHom_comp L.op hhom))
  have hpt : _ = op (L.obj X) := hZ'
  exact ⟨Z, hobj, hZ, ⟨hpt ▸ ed.homotopyEquiv⟩⟩

end Stacks.Cobar

end
