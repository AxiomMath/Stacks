module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.DegreeZero
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.PowerExact
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Presentations of the symmetric powers, and quasi-coherence of them

Let `G` be a sheaf of modules on a ringed site with a global presentation `G₂ ⟶ G₁ ⟶ G ⟶ 0`, where
`G₁` and `G₂` are free. In every degree `n = 1 + k` with `k ≥ 0` there is an exact sequence

`G₂ ⊗ Sym^k(G₁) ⟶ Symⁿ(G₁) ⟶ Symⁿ(G) ⟶ 0`,

whose two outer terms are again free, so `Symⁿ(G)` has a global presentation; in degree zero the
symmetric piece is the structure sheaf. Consequently every symmetric power of a quasi-coherent
sheaf of modules on a scheme is quasi-coherent, which is the case of symmetric powers in clause (5)
of Tag 01CK.

## Main definitions

* `Stacks.SymmetricFree.tensorSheafFreeIso`: the tensor product of two free sheaves of modules is
  free on the product of the index sets.
* `SheafOfModules.symmetricPiecePresentationSucc` and `SheafOfModules.symmetricPiecePresentation`:
  a global presentation of `Symⁿ(G)` out of one of `G`, in a positive degree and then in every
  nonnegative degree.
* `Stacks.RelativeProj.symmetricSituationOfQuasicoherent`: the relative `Proj` situation of the
  symmetric algebra of a quasi-coherent sheaf of modules on a scheme, whose relative `Proj` is the
  projective bundle.

## Main results

* `Stacks.SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece`: every homogeneous piece of
  nonnegative degree of the symmetric algebra of a quasi-coherent sheaf of modules on a scheme is
  quasi-coherent.

## Implementation notes

Quasi-coherence is stated on a scheme rather than over a ringed site because
`SheafOfModules.QuasicoherentData.shrink` produces an index type in the universe of the objects of
the site, while `Stacks.SliceAlgebra.isQuasicoherent_piece_of_presentations` asks for one in the
universe of the modules; on a scheme the two coincide.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe v u w

namespace Stacks.SymmetricFree

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max v u, w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The tensor product of two free sheaves of modules is free**: the tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` of `SheafOfModules.free I` and `SheafOfModules.free K`
is isomorphic to `SheafOfModules.free (I × K)`. -/
noncomputable def tensorSheafFreeIso (I K : Type w) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj
        (SheafOfModules.free I)).obj
      (SheafOfModules.free K) ≅
      SheafOfModules.free (R := toRingCat J Osharp) (I × K) :=
  Stacks.SheafOfModules.TensorProduct.freeTensorIso Osharp I K

end Stacks.SymmetricFree

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max v u, w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (G : SheafOfModules.{w} (toRingCat J Osharp))

/-- **A global presentation of `Sym^{1+k}(G)` out of a global presentation of `G`.** The generators
are the degree-`(1 + k)` monomials in the generators of `G`, and the relations are indexed by the
relations of `G` times the degree-`k` monomials in its generators. -/
noncomputable def symmetricPiecePresentationSucc (P : G.Presentation) (k : ℕ) :
    ((sheafifiedSymmetricAlgebra J G).piece (1 + (k : ℤ))).Presentation := by
  letI : Epi P.generators.π := P.generators.epi
  set M₁ : SheafOfModules.{w} (toRingCat J Osharp) := free P.generators.I with hM₁
  set p : M₁ ⟶ G := P.generators.π with hp
  set q : free P.relations.I ⟶ M₁ := P.relations.π ≫ kernel.ι p with hq
  have hqp : q ≫ p = 0 := by rw [hq, Category.assoc, kernel.condition, comp_zero]
  have hex : (ShortComplex.mk q p hqp).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    convert P.isColimit using 1
  have hS := exact_and_epi_symmetricPresentationShortComplex q p hqp hex (k : ℤ)
    (1 + (k : ℤ)) (by positivity) rfl
  set S := GradedAlgebra.symmetricPresentationShortComplex
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁)
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J G).isUniversal.1 q p hqp (k : ℤ)
      (1 + (k : ℤ)) rfl with hSdef
  have hdeg : (1 + (k : ℤ)) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  set e₂ : S.X₂ ≅ free (R := toRingCat J Osharp)
        {d : P.generators.I →₀ ℕ | Finsupp.degree d = k + 1} :=
    eqToIso (congrArg (sheafifiedSymmetricAlgebra J M₁).piece hdeg) ≪≫
      Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso J P.generators.I (k + 1) with he₂
  set e₁ : S.X₁ ≅ free (R := toRingCat J Osharp)
        (P.relations.I × {d : P.generators.I →₀ ℕ | Finsupp.degree d = k}) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj
        (free P.relations.I)).mapIso
      (Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso J P.generators.I k) ≪≫
      Stacks.SymmetricFree.tensorSheafFreeIso J _ _ with he₁
  set f := e₁.inv ≫ S.f ≫ e₂.hom with hf
  set g := e₂.inv ≫ S.g with hg
  have hfg : f ≫ g = 0 := by
    rw [hf, hg, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, S.zero, comp_zero]
  have hiso : S ≅ ShortComplex.mk f g hfg :=
    ShortComplex.isoMk e₁ e₂ (Iso.refl _) (by simp [hf]) (by simp [hg])
  have hex' : (ShortComplex.mk f g hfg).Exact := ShortComplex.exact_of_iso hiso hS.1
  haveI : Epi S.g := hS.2
  haveI : Epi g := by rw [hg]; infer_instance
  exact presentationOfIsCokernelFree f g hfg
    ((ShortComplex.mk f g hfg).exact_and_epi_g_iff_g_is_cokernel.1
      ⟨hex', inferInstance⟩).some

/-- **A global presentation of `Symⁿ(G)` out of a global presentation of `G`**, in every
nonnegative degree. In a positive degree it is `SheafOfModules.symmetricPiecePresentationSucc`; in
degree zero, where the symmetric piece is the structure sheaf, it is
`SheafOfModules.sheafifiedSymmetricPieceZeroPresentation`. -/
noncomputable def symmetricPiecePresentation (P : G.Presentation) (n : ℕ) :
    ((sheafifiedSymmetricAlgebra J G).piece (n : ℤ)).Presentation := by
  obtain _ | k := n
  · exact sheafifiedSymmetricPieceZeroPresentation J G
  · exact Presentation.ofIsIso
      (eqToHom (congrArg (sheafifiedSymmetricAlgebra J G).piece
        (by push_cast; ring : (1 + (k : ℤ)) = ((k + 1 : ℕ) : ℤ))))
      (symmetricPiecePresentationSucc J G P k)

end SheafOfModules

namespace Stacks

open _root_.AlgebraicGeometry TopologicalSpace _root_.SheafOfModules

/-- **Symmetric powers of a quasi-coherent module are quasi-coherent.** For a quasi-coherent sheaf
of modules `F` on a scheme `X` and `n : ℕ`, the degree-`n` piece of the symmetric algebra of `F` is
quasi-coherent. -/
@[stacks 01CK "symmetric powers of a quasi-coherent module"]
theorem SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) F).piece
      (n : ℤ)).IsQuasicoherent :=
  SliceAlgebra.isQuasicoherent_piece_of_symmetricPowerPresentations X F (n : ℤ)
    fun _ _ P => symmetricPiecePresentation _ _ P n

/-- **The projective bundle situation of a quasi-coherent sheaf of modules**: the relative `Proj`
situation `Stacks.RelativeProj.symmetricSituation` of the symmetric algebra of `F`, with the
quasi-coherence of its pieces given by
`Stacks.SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece`. -/
noncomputable def RelativeProj.symmetricSituationOfQuasicoherent (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] : RelativeProj.Situation.{u} :=
  RelativeProj.symmetricSituation X F
    fun n => SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece X F n

end Stacks

end
