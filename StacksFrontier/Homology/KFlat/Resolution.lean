module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Triangle
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# K-flat resolutions and K-flat factorizations

Let `R` be a commutative ring. Every cochain complex of `R`-modules receives a
termwise-surjective quasi-isomorphism from a K-flat complex whose terms are flat modules
(Stacks 06Y4). Consequently every morphism out of a K-flat complex factors, up to homotopy,
through a K-flat complex which maps to the target by a quasi-isomorphism (Stacks 0G6M).

## Main results

* `CochainComplex.KFlat.exists_kFlat_resolution`: every cochain complex of `R`-modules admits a
  termwise-surjective quasi-isomorphism from a K-flat complex with flat terms.
* `CochainComplex.KFlat.exists_kFlat_representative`: every object of the derived category of
  `R`-modules is isomorphic to the image of a K-flat cochain complex.
* `CochainComplex.KFlat.exists_kFlat_factorization_up_to_homotopy`: a morphism from a K-flat
  complex factors up to homotopy through a K-flat complex mapping to the target by a
  quasi-isomorphism, and the intermediate complex has flat terms as soon as the source does.
* `CochainComplex.KFlat.exists_factorization_of_quasiIso_toMappingCone`: the construction
  behind that factorization, in an arbitrary abelian category and with the K-flatness
  hypotheses stripped off — a quasi-isomorphism into the mapping cone of `h : Q ⟶ L`
  produces a factorization of `h` through a quasi-isomorphism onto `L`, together with the
  distinguished triangle and the termwise biproduct decomposition along which properties of
  `Q` and of the resolving complex transfer to the intermediate complex.

## Implementation notes

The resolution is produced for `R : Type u` and modules in `Type (max u v)`, independent
universes, so its K-flatness is `CochainComplex.KFlat`; the factorization, which passes
through a mapping cone in the same category as its input, is stated where the ring and the
modules share a universe. Termwise surjectivity is expressed on the underlying functions of the
component linear maps, and homotopy by the nonemptiness of Mathlib's type of chain homotopies.

The resolution of Stacks 06Y4 is built as the sequential colimit of the ladder of complexes
resolving the truncations `τ_{≤ n} M` by bounded-above complexes of projectives, which are
K-flat by Stacks 064K; K-flatness passes to the colimit by Stacks 06Y3, flatness of the terms
by `colimit_flat_of_flat`, and the comparison map is a quasi-isomorphism because in each fixed
degree the homology of the ladder is eventually constant.

The factorization of Stacks 0G6M glues a K-flat resolution `q : M ⟶ C(a)` of the mapping cone
of `a` onto the source: the intermediate complex is the extension of the source by `M` twisted
by the first component of `q`, degreewise the biproduct with a differential corrected by a
twisting cochain. That extension sits in a degreewise split short exact sequence, whence a
distinguished triangle to which the two-out-of-three property of Stacks 06Y2 applies.

## References

* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [The Stacks Project, Tag 0G6M](https://stacks.math.columbia.edu/tag/0G6M)
-/

open CategoryTheory

universe u v w x

open Stacks.HomologyColimit

namespace CochainComplex.KFlat

/-! ### K-flat resolutions (Stacks 06Y4) -/

section Resolution

open Limits

section HomologyColimit

variable {A : Type v} [Category.{w} A] [Abelian A]

end HomologyColimit

/-- **A sequential colimit of flat modules is flat**, by Stacks 05UT read on the direct limit of
the directed system of its values: the colimit of `F : ℕ ⥤ ModuleCat R` is the direct limit of
the system `F.obj n` over `ULift ℕ`, and `colimit_flat_of_flat` applies to that. -/
lemma flat_colimit {R : Type u} [CommRing R] (F : ℕ ⥤ ModuleCat.{max u x} R)
    (hF : ∀ n, Module.Flat R (F.obj n)) :
    Module.Flat R (CategoryTheory.Limits.colimit F : ModuleCat R) := by
  let E : ULift.{max u x} ℕ ≌ ℕ := ULift.orderIso.equivalence
  let G : ULift.{max u x} ℕ ⥤ ModuleCat.{max u x} R := E.functor ⋙ F
  let f : (i j : ULift.{max u x} ℕ) → i ≤ j → (G.obj i : Type (max u x)) →ₗ[R] G.obj j :=
    fun i j h => (G.map (homOfLE h)).hom
  let : DirectedSystem (fun i => (G.obj i : Type (max u x)))
      (fun {_ _} h => f _ _ h) := by
    refine ⟨fun _ y => by simp [f], fun a b d hab hbd y => ?_⟩
    have h : G.map (homOfLE (hab.trans hbd)) =
        G.map (homOfLE hab) ≫ G.map (homOfLE hbd) := by
      rw [← G.map_comp]
      congr 1
    exact (congr($h y)).symm
  let _ : ∀ i, Module.Flat R (G.obj i) := fun i => hF i.down
  have hd : Module.Flat R (Module.DirectLimit (fun i => (G.obj i : Type (max u x))) f) :=
    colimit_flat_of_flat (fun i => (G.obj i : Type (max u x))) f
  let c := (Limits.colimit.cocone F).whisker E.functor
  have hc : IsColimit c := (Limits.colimit.isColimit F).whiskerEquivalence E
  let e := ((ModuleCat.directLimitIsColimit (R := R)
    (fun i => (G.obj i : Type (max u x))) f).coconePointUniqueUpToIso hc).toLinearEquiv
  exact @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ hd e.symm

/-- **Stacks 06Y4.** Every cochain complex of modules admits a termwise-surjective
quasi-isomorphism from a K-flat complex with flat terms. -/
@[stacks 06Y4]
theorem exists_kFlat_resolution {R : Type u} [CommRing R]
    (M : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (f : K ⟶ M),
      K.KFlat ∧
        (∀ n : ℤ, Module.Flat R (K.X n)) ∧
        QuasiIso f ∧
        ∀ n : ℤ, Function.Surjective (f.f n).hom := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := fun X => Projective X
  let : P.ContainsZero := ⟨ModuleCat.of R (Fin 0 → ULift.{v} R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hsum : ∀ X Y : ModuleCat.{max u v} R, P X → P Y → P (X ⊞ Y) := by
    intro X Y hX hY
    change Projective X at hX
    change Projective Y at hY
    let := hX
    let := hY
    infer_instance
  have hcover : ∀ X : ModuleCat.{max u v} R, ∃ (Y : ModuleCat.{max u v} R) (_ : P Y)
      (p : Y ⟶ X), Epi p := by
    intro X
    exact ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  obtain ⟨Q, q, g, hq, hepi, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover M
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk M
    (NatTrans.ofSequence (fun n => q n ≫ M.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ M := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ M.ιTruncLE (n : ℤ) := fun n => hc.fac s n
  have hqi : QuasiIso α :=
    let : AB5OfSize.{0, 0, max u v, max u v + 1} AddCommGrpCat.{max u v} :=
      AB5OfSize_of_univLE.{0, 0, max u v, max u v} AddCommGrpCat.{max u v}
    let : HasExactColimitsOfShape ℕ (ModuleCat.{max u v} R) :=
      HasExactColimitsOfShape.domain_of_functor ℕ
        (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα
  have hQflat : ∀ n i, Module.Flat R ((Q n).X i) := fun n i => by
    let : Projective ((Q n).X i) := hflat n i
    infer_instance
  have hkQ : ∀ n, (Q n).KFlat := by
    intro n
    let : (Q n).IsStrictlyLE (n : ℤ) := hle n
    let := hQflat n
    exact kFlat_of_flat (Q n) n
  have hk : c.pt.KFlat := kFlat_colimit D hkQ
  have hterms : ∀ i : ℤ, Module.Flat R (c.pt.X i) := by
    intro i
    have ht : Module.Flat R (colimit (D ⋙ HomologicalComplex.eval _ _ i) : ModuleCat R) :=
      flat_colimit _ fun n => hQflat n i
    exact @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ ht
      (preservesColimitIso (HomologicalComplex.eval _ _ i) D).toLinearEquiv
  refine ⟨c.pt, α, hk, hterms, hqi, ?_⟩
  intro i
  rw [← ModuleCat.epi_iff_surjective]
  let n := i.toNat + 1
  have hi : i ≤ (n : ℕ) := by dsimp [n]; omega
  have : Epi ((q n).f i) := hepi n i
  have hpre : (ComplexShape.embeddingUpIntLE (n : ℤ)).op.f
      ((n : ℤ) - i).natAbs = i := by
    change (n : ℤ) - (((n : ℤ) - i).natAbs : ℤ) = i
    omega
  have hnotboundary : ¬ (ComplexShape.embeddingUpIntLE (n : ℤ)).op.BoundaryGE
      ((n : ℤ) - i).natAbs := by
    rw [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    have hdiff : 0 < (n : ℤ) - i := by dsimp [n]; omega
    simpa only [Int.natAbs_eq_zero] using
      (show (n : ℤ) - i ≠ 0 by omega)
  have : IsIso ((M.op.πTruncGE
      (ComplexShape.embeddingUpIntLE (n : ℤ)).op).f i) := by
    dsimp only [HomologicalComplex.πTruncGE, HomologicalComplex.truncGE]
    rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ hpre]
    exact M.op.isIso_restrictionToTruncGE' _ _ hnotboundary
  have : IsIso ((M.ιTruncLE (n : ℤ)).f i) := by
    change IsIso ((M.op.πTruncGE
      (ComplexShape.embeddingUpIntLE (n : ℤ)).op).f i).unop
    infer_instance
  have : Epi ((c.ι.app n).f i ≫ α.f i) := by
    rw [← HomologicalComplex.comp_f, hα n, HomologicalComplex.comp_f]
    exact (epi_comp_iff_of_isIso _ _).2 (hepi n i)
  exact epi_of_epi ((c.ι.app n).f i) (α.f i)

end Resolution

/-! ### K-flat representatives of objects of the derived category -/

section Representative

/-- Every object of the derived category of `R`-modules is isomorphic to the image of a K-flat
cochain complex: any complex representing it admits a K-flat resolution, which is a
quasi-isomorphism and therefore becomes invertible in the derived category.

The hom-universe `w` of the derived category and the module universe `max u v` are left
independent of one another, so this covers every instantiation in use, including the standard
derived category `HasDerivedCategory.standard`. -/
theorem exists_kFlat_representative {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (X : DerivedCategory (ModuleCat.{max u v} R)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.KFlat ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, f, hP, -, hf, -⟩ :=
    exists_kFlat_resolution (DerivedCategory.Q.objPreimage X)
  have := hf
  exact ⟨P, hP,
    ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

end Representative

/-! ### Factoring a morphism through a K-flat complex (Stacks 0G6M) -/

section Factorization

open Pretriangulated

section Glue

open _root_.CochainComplex
open Category Preadditive HomologicalComplex Limits

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] HasDerivedCategory.standard

variable {Q R L : CochainComplex A ℤ} (h : Q ⟶ L) (u : R ⟶ mappingCone h)
/-- **A quasi-isomorphism into a mapping cone factors the map it is the cone of.**

Let `h : Q ⟶ L` be a map of cochain complexes in an abelian category and let
`u : R ⟶ C(h)` be a quasi-isomorphism into its mapping cone. Then `h` factors as
`b ≫ c` with `c : N ⟶ L` a quasi-isomorphism, where `N` is the extension of `Q` by `R`
twisted by the first component of `u`: its degree `p` term is `Q^p ⊞ R^p`, and `N` sits
with `Q` and `R` in a distinguished triangle of `K(A)`, namely the one attached to the
degreewise split short exact sequence `0 ⟶ Q ⟶ N ⟶ R ⟶ 0`.

The three pieces of data beyond the factorization itself are what a consumer needs in
order to transfer a two-out-of-three property along the construction: the triangle
transfers properties stable in distinguished triangles, and the termwise biproduct
transfers termwise properties. This is how Stacks 0G6M and its sheaf-theoretic counterpart
Stacks 0G6V are both deduced. -/
theorem exists_factorization_of_quasiIso_toMappingCone
    {Q R L : CochainComplex A ℤ} (h : Q ⟶ L) (u : R ⟶ mappingCone h) (hu : QuasiIso u) :
    ∃ (N : CochainComplex A ℤ) (b : Q ⟶ N) (g : N ⟶ R) (c : N ⟶ L)
      (_ : ∀ p : ℤ, N.X p ≅ Q.X p ⊞ R.X p)
      (δ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R ⟶
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Q)⟦(1 : ℤ)⟧),
      b ≫ c = h ∧ QuasiIso c ∧
        Triangle.mk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map b)
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) δ ∈
          distTriang (HomotopyCategory A (ComplexShape.up ℤ)) :=
  ⟨glue h u, glueIn h u, gluePr h u, glueDesc h u, fun _ => Iso.refl _,
    (CochainComplex.trianglehOfDegreewiseSplit (glueSC h u) (glueSplitting h u)).mor₃,
    glueIn_glueDesc h u, quasiIso_glueDesc h u hu,
    CochainComplex.trianglehOfDegreewiseSplit_distinguished (glueSC h u) (glueSplitting h u)⟩

end Glue

private lemma flat_prod {R A B : Type u} [CommRing R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [Module.Flat R A] [Module.Flat R B] : Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ S x y hxy
  have key (C : Type u) [AddCommMonoid C] [Module R C] [Module.Flat R C]
      (π : A × B →ₗ[R] C) : π.lTensor S x = π.lTensor S y := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C) S.subtype
      Subtype.val_injective
    have := congrArg (π.lTensor P) hxy
    simpa only [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor] using this
  have hpr (z : TensorProduct R S (A × B)) : TensorProduct.prodRight R R S A B z =
      ((LinearMap.fst R A B).lTensor S z, (LinearMap.snd R A B).lTensor S z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp_all
  apply (TensorProduct.prodRight R R S A B).injective
  rw [hpr, hpr]
  exact Prod.ext (key A _) (key B _)

/-- A morphism from a K-flat complex factors up to homotopy through another K-flat complex
which maps to the target by a quasi-isomorphism. When the source has flat terms, the intermediate
complex can be chosen with flat terms. -/
@[stacks 0G6M]
theorem exists_kFlat_factorization_up_to_homotopy
    {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ L)
    (hK : K.KFlat) :
    ∃ (N : CochainComplex (ModuleCat.{u} R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      N.KFlat ∧
        QuasiIso c ∧
        Nonempty (Homotopy a (b ≫ c)) ∧
        ((∀ n : ℤ, Module.Flat R (K.X n)) → ∀ n : ℤ, Module.Flat R (N.X n)) := by
  let C := CochainComplex.mappingCone a
  obtain ⟨M, q, hM, hMflat, hq, _⟩ := exists_kFlat_resolution C
  let N := glue a q
  let b := glueIn a q
  let c := glueDesc a q
  have hc : QuasiIso c := quasiIso_glueDesc a q hq
  refine ⟨N, b, c, ?_, hc, ⟨Homotopy.ofEq (glueIn_glueDesc a q).symm⟩, ?_⟩
  · exact (kFlat_two_out_of_three_of_distTriang _ _ _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished
        (glueSC a q) (glueSplitting a q))).2.1 hK hM
  · intro hKflat n
    change Module.Flat R (↑((K.X n) ⊞ (M.X n) : ModuleCat R))
    let := hKflat n
    let := hMflat n
    let : Module.Flat R (K.X n × M.X n) := flat_prod
    let e := ModuleCat.biprodIsoProd (K.X n) (M.X n)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Factorization

end CochainComplex.KFlat

end
