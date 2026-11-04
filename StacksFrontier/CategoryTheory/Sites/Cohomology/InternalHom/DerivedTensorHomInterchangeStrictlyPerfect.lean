module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# The interchange morphism of Stacks 0BYU is invertible at a strictly perfect source

Let `(C, 𝒪)` be a ringed site. Stacks 0BYU supplies the canonical morphism

`Φ_{K, L, M} : K ⊗^𝐋_𝒪 R𝑆heafHom(M, L) ⟶ R𝑆heafHom(M, K ⊗^𝐋_𝒪 L)`,

`AlgebraicGeometry.RingedSite.derivedTensorHomInterchange`. This file proves that it is
**invertible whenever `M` is the class of a strictly perfect complex** — a complex with
finitely many nonzero terms, each a direct summand of a finite free `𝒪`-module — for arbitrary
`K` and `L`.

The proof is the one the source of Stacks 0ATN calls clear, run through the two inputs the
library already has. On a model triple `(A, I, C)` with `A` K-flat and `I` K-injective,
`AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_comparison` identifies `Φ` with the
class of the morphism of complexes

`Tot(A ⊗_𝒪 𝑆heafHom(C, I)) ⟶ 𝑆heafHom(C, Tot(A ⊗_𝒪 I)) ⟶ 𝑆heafHom(C, J)`,

the interchange morphism of complexes of Stacks 0BYT followed by the augmentation of
`Tot(A ⊗_𝒪 I)` into its chosen K-injective resolution `J`. Both factors are quasi-isomorphisms
at a strictly perfect `C`: the first is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`, and the
second is `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`, which says
that `𝑆heafHom(C, -)` carries a quasi-isomorphism of targets to a quasi-isomorphism when `C` is
strictly perfect. The passage from a model triple to an arbitrary pair `(K, L)` is naturality:
`Φ` is a natural transformation of trifunctors, so its invertibility at a triple depends only on
the isomorphism class of that triple, and a K-flat representative of `K` and a K-injective
representative of `L` always exist.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomInterchange_model`: invertibility of `Φ`
  at a model triple with strictly perfect internal-Hom source.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomInterchange_of_isFiniteFreeSummand`:
  **invertibility of `Φ` at an arbitrary `K` and `L` and a strictly perfect `M`.**

## Implementation notes

The boundedness hypothesis is `{i | ¬ IsZero (C.X i)}.Finite`, the spelling both inputs use,
rather than a window `[a, b)`; the two inputs reduce it to a window themselves.

Nothing here carries a Stacks attribute. The invertibility statement of Stacks 0BYU is not part
of that tag — 0BYU asserts only the morphism and its functoriality, both already attributed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange` — and the
invertibility of the *other* canonical map `K ⊗^𝐋_𝒪 M^∨ ⟶ R𝑆heafHom(M, K)` of Stacks 08JD,
which is clause 3 of Stacks 08JJ, is a statement about
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` and is not what is proved here: no
lemma of the library identifies the two canonical maps, the one being built from the derived
composition morphism of Stacks 0A98 and the other from the interchange morphism of complexes of
Stacks 0BYT. What the statements below give is a comparison with the *same source and target*
as clause 3 of Stacks 08JJ once `L` is taken to be the structure sheaf, which is all that the
formula of Stacks 0A0E needs; see
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDual`.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## References

* [Stacks Project, Tag 0BYU](https://stacks.math.columbia.edu/tag/0BYU)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The morphism of complexes which computes the interchange morphism of Stacks 0BYU at a
model triple is a quasi-isomorphism at a strictly perfect internal-Hom source.** It is the
interchange morphism of complexes of Stacks 0BYT followed by the K-injective resolution
augmentation, and each factor is a quasi-isomorphism: the first by
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand` and the
second by `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`. -/
theorem quasiIso_interchangeComplexMap_of_isFiniteFreeSummand
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (C.X i)) :
    QuasiIso (tensorHomInterchange X A I C ≫
      homMap X (𝟙 C) ((kInjectiveAugmentation X).app (tensorTotal X A I))) := by
  have : QuasiIso (tensorHomInterchange X A I C) :=
    tensorHomInterchange_quasiIso_of_isFiniteFreeSummand X A I C hbdd hterm
  have : QuasiIso (homMap X (𝟙 C) ((kInjectiveAugmentation X).app (tensorTotal X A I))) :=
    homMap_quasiIso_of_isFiniteFreeSummand X
      ((kInjectiveAugmentation X).app (tensorTotal X A I)) C hbdd hterm
  infer_instance

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The interchange morphism of Stacks 0BYU is invertible at a model triple whose
internal-Hom source is strictly perfect.** `A` is K-flat and `I` is K-injective, so
`AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_comparison` writes the morphism as the
class of a morphism of complexes between two identifications, and that morphism of complexes is
a quasi-isomorphism by
`AlgebraicGeometry.RingedSite.quasiIso_interchangeComplexMap_of_isFiniteFreeSummand`. -/
@[sga "5 III 6.3" "special case", sga "6 I 7.6" "special case"]
theorem isIso_derivedTensorHomInterchange_model
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    (hbdd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (C.X i)) :
    IsIso (derivedTensorHomInterchange X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)
      (DerivedCategory.Q.obj C)) := by
  have hq : IsIso (DerivedCategory.Q.map (tensorHomInterchange X A I C ≫
      homMap X (𝟙 C) ((kInjectiveAugmentation X).app (tensorTotal X A I)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_interchangeComplexMap_of_isFiniteFreeSummand X A I C hbdd hterm)
  have hsrc : IsIso (interchangeSourceIso X A I C hA).hom :=
    (interchangeSourceIso X A I C hA).isIso_hom
  have htgt : IsIso (interchangeTargetIso X A I C hA).hom :=
    (interchangeTargetIso X A I C hA).isIso_hom
  have hfg : IsIso (derivedTensorHomInterchange X (DerivedCategory.Q.obj A)
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj C) ≫
        (interchangeTargetIso X A I C hA).hom) := by
    rw [derivedTensorHomInterchange_comparison X A I C hA]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hsrc hq
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ htgt hfg

/-- **The interchange morphism of Stacks 0BYU is invertible at a strictly perfect
internal-Hom source**, for arbitrary objects `K` and `L` of `D(𝒪)`:

`K ⊗^𝐋_𝒪 R𝑆heafHom(C, L) ≅ R𝑆heafHom(C, K ⊗^𝐋_𝒪 L)` for `C` strictly perfect.

The interchange morphism is a natural transformation of trifunctors, so its invertibility at a
triple of objects of `D(𝒪)` only depends on the isomorphism class of that triple. The triple
`(K, L, C)` is isomorphic to the model triple built from the chosen K-flat representative of
`K`, the chosen K-injective representative of `L` and `C` itself — the third slot is left alone,
which is what keeps `C` strictly perfect — and there the invertibility is
`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomInterchange_model`. -/
theorem isIso_derivedTensorHomInterchange_of_isFiniteFreeSummand
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (C.X i)) :
    IsIso (derivedTensorHomInterchange X K L (DerivedCategory.Q.obj C)) := by
  have e : (interchangeModelTriple X (kFlatModel X K) (kInjectiveModel X L) C :
      interchangeTriples X) ≅ (K, L, op (DerivedCategory.Q.obj C)) :=
    (kFlatModelIso X K).prod ((kInjectiveModelIso X L).prod
      (Iso.refl (op (DerivedCategory.Q.obj C))))
  have hmodel : IsIso ((derivedTensorHomInterchangeNatTrans X).app
      (interchangeModelTriple X (kFlatModel X K) (kInjectiveModel X L) C)) :=
    isIso_derivedTensorHomInterchange_model X (kFlatModel X K) (kInjectiveModel X L) C
      (isKFlat_kFlatModel X K) hbdd hterm
  exact (NatTrans.isIso_app_iff_of_iso (derivedTensorHomInterchangeNatTrans X) e).1 hmodel

end AlgebraicGeometry.RingedSite

end
