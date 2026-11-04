module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackPreservesQuasiCoherent

/-!
# The base-change data of a morphism of ringed topoi on categories

Let `C` and `C'` be categories viewed as sites with the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat`
and `O' : C'ᵒᵖ ⥤ RingCat` be sheaves of rings on them with commutative section rings, and let a
functor `F : C' ⥤ C` together with `φ : F⁻¹O ⟶ O'` be the datum of a morphism of ringed topoi
`g : (Sh(C'), O') → (Sh(C), O)`.

Three derived base changes are attached to this situation: `- ⊗^L_{O(V)} O(U)` along a
restriction homomorphism of `O`, the same for `O'`, and `- ⊗^L_{O(F U')} O'(U')` along the
structure homomorphism of `g` at an object `U'` of `C'`. Each is characterized as the left
adjoint of the corresponding derived restriction of scalars, and each is constructed here from
derived extension of scalars along a homomorphism of commutative rings. In particular the
cartesian condition on `D(O)` and on `D(O')`, and the base-change square of `g`, are all available
with no base-change datum assumed.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.dBaseChange`: derived base change
  `- ⊗^L_R S` along a homomorphism `R ⟶ S` of rings with commutative underlying rings.
* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.baseChangeDataOfComm`: the derived
  base-change datum of a sheaf of rings with commutative section rings, in an arbitrary module
  universe.
* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.structureBaseChange`: the derived
  base changes along the structure homomorphisms `O(F U') ⟶ O'(U')` of `g`.
* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.qcPullbackOfComm`: the functor
  `QC(O) ⥤ QC(O')` induced by a derived pullback along `g`.

## Main results

* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.dBaseChangeAdj`: derived base change
  along a homomorphism of commutative rings is left adjoint to derived restriction of scalars.
* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.isQC_iff_of_baseChangeData`: the
  cartesian condition does not depend on the base-change datum with respect to which it is taken.
* `Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.isQC_Lpullback_of_comm`: a derived
  pullback along `g` carries objects with cartesian derived sections to objects with cartesian
  derived sections, the cartesian condition being taken on both sides with respect to the
  base-change data constructed here.

## Implementation notes

Derived extension of scalars is available for homomorphisms of *commutative* rings only, extension
of scalars along a homomorphism of general rings being absent from the ambient library.
Accordingly the constructions below carry the hypothesis that every section ring of `O` and of
`O'` is commutative, which is the standing convention of the source; the ring objects themselves
stay in `RingCat`, as in the statement of the cartesian condition, and the commutative structure
is introduced locally where the tensor product requires it. This is the same arrangement as for
the base-change datum of a single sheaf of rings, which this file reproduces in an arbitrary
module universe and over an arbitrary ring universe: the two-site situation forces the module
universe to contain both site universes, so the datum of `O` is needed in the module universe of
`C'` and conversely, which fixes a module universe different from the one either site determines
on its own.

What is not constructed here is the derived pullback `Lg^*` itself, which stays the datum
`DerivedPullbackData`, carrying the functor together with the computation
`RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^L_{O(F U')} O'(U')` of its derived sections and the compatibility
of that computation with the canonical derived restriction maps. So `isQC_Lpullback_of_comm`,
which carries the attribute of Lemma 21.43.10, proves that lemma only for a derived pullback
supplied with its sections computation: what is established is the implication from that
computation to the preservation of the cartesian condition.

UNIVERSES. `dBaseChange` is stated with the module universe written as `max t r`, `r` being the
ring universe: derived extension of scalars along a homomorphism of rings in `Type r` produces
modules in `max t r` for an arbitrary `t`, and every application below chooses `t` so that
`max t r` is the module universe of the ambient derived category. For the datum of `O` that
universe is `max u v r w` with `w` the module universe parameter of `D(O)`, so `t` is `max u v w`;
for the structure homomorphisms of `g` it is `max u v u' v' r`, the smallest universe containing
both site universes and the ring universe, so `t` is `max u v u' v'`.

## References

* [Stacks Project, Lemma 21.43.10 (Tag 0GZ1)](https://stacks.math.columbia.edu/tag/0GZ1)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.CartesianObjects (commRingOfComm dRestrictCompIso)
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

universe r v u v' u' t w

namespace Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

attribute [local instance] HasDerivedCategory.standard

section Rings

variable {R S : RingCat.{r}} (ψ : R ⟶ S) (hR : ∀ x y : R, x * y = y * x)
  (hS : ∀ x y : S, x * y = y * x)

/-- **Derived base change along a homomorphism of rings with commutative underlying rings.** The
total left derived functor `- ⊗^L_R S : D(R) ⥤ D(S)` of extension of scalars along `ψ`. -/
def dBaseChange :
    DerivedCategory (ModuleCat.{max t r} R) ⥤ DerivedCategory (ModuleCat.{max t r} S) :=
  let := commRingOfComm R hR
  let := commRingOfComm S hS
  (totalDerivedExtensionScalars.{r, r, t} ψ.hom).functor

/-- **Tag 0GMT.** Derived base change along `ψ` is left adjoint to derived restriction of scalars
along `ψ`, which is what characterizes it up to unique natural isomorphism. -/
def dBaseChangeAdj : dBaseChange.{r, t} ψ hR hS ⊣ dRestrictScalars.{r, max t r} ψ := by
  let := commRingOfComm R hR
  let := commRingOfComm S hS
  have : Functor.IsLeftDerivedFunctor
      (totalDerivedExtensionScalars.{r, r, t} ψ.hom).functor
      (show DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{r, r, t} ψ.hom).functor ⟶
          (ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q from
        (totalDerivedExtensionScalars.{r, r, t} ψ.hom).comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{max t r} R) (ComplexShape.up ℤ)) :=
    (totalDerivedExtensionScalars.{r, r, t} ψ.hom).isLeftDerived
  exact derivedExtensionScalarsAdjunction.{r, r, t} ψ.hom
    (totalDerivedExtensionScalars.{r, r, t} ψ.hom).functor
    (totalDerivedExtensionScalars.{r, r, t} ψ.hom).comparison

end Rings

section OneSite

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)

/-- The canonical comparison map attached to a morphism of `Cᵒᵖ` does not depend on the
base-change datum: the two base changes along `a` are left adjoints of one and the same derived
restriction of scalars, and the comparison maps correspond under the resulting isomorphism of
left adjoints. -/
theorem comparison_eq_leftAdjointUniq (bc₁ bc₂ : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U)
    (K : DMod.{w} O) :
    comparison.{w} bc₁ a K =
      (Adjunction.leftAdjointUniq (bc₁.baseChangeAdj a) (bc₂.baseChangeAdj a)).hom.app
          ((RGamma.{w} O V).obj K) ≫
        comparison.{w} bc₂ a K := by
  have hnat := (Adjunction.leftAdjointUniq (bc₁.baseChangeAdj a)
    (bc₂.baseChangeAdj a)).hom.naturality (restrictionMap.{w} O a K)
  simp only [comparison, Adjunction.homEquiv_counit]
  rw [← reassoc_of% hnat, Adjunction.leftAdjointUniq_hom_app_counit]

/-- **The cartesian condition of tag 0GYV does not depend on the base-change datum.** Since every
base change is characterized as a left adjoint of derived restriction of scalars, the comparison
maps for two data differ by an isomorphism, so they are invertible together. -/
theorem isQC_iff_of_baseChangeData (bc₁ bc₂ : BaseChangeData.{w} O) (K : DMod.{w} O) :
    IsQC.{w} bc₁ K ↔ IsQC.{w} bc₂ K := by
  constructor <;> intro h U V a
  · rw [comparison_eq_leftAdjointUniq O bc₂ bc₁ a K]
    have := h a
    infer_instance
  · rw [comparison_eq_leftAdjointUniq O bc₁ bc₂ a K]
    have := h a
    infer_instance

/-- **Tag 0GYV, base-change datum, over arbitrary ring and module universes.** The derived
extension-of-scalars functors along all restriction homomorphisms of `O`, with their adjunctions
to derived restriction of scalars and their composition isomorphisms. The functoriality
isomorphism of tag 0FNG is obtained by conjugating the composition isomorphism of the right
adjoints. -/
def baseChangeDataOfComm : BaseChangeData.{w} O where
  baseChange a := dBaseChange.{r, max u v w} (O.map a) (hO _) (hO _)
  baseChangeAdj a := dBaseChangeAdj.{r, max u v w} (O.map a) (hO _) (hO _)
  baseChangeComp a b :=
    (conjugateIsoEquiv
      ((dBaseChangeAdj.{r, max u v w} (O.map a) (hO _) (hO _)).comp
        (dBaseChangeAdj.{r, max u v w} (O.map b) (hO _) (hO _)))
      (dBaseChangeAdj.{r, max u v w} (O.map (a ≫ b)) (hO _) (hO _))).symm
      (dRestrictCompIso.{r, u, v, w} O a b)

end OneSite

section Setting

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)
  (hO' : ∀ (U' : C'ᵒᵖ) (x y : O'.obj U'), x * y = y * x)

/-- **The derived base changes along the structure homomorphisms of a morphism of ringed topoi.**
For each object `U'` of `C'` the derived base change `- ⊗^L_{O(F U')} O'(U')`, with its adjunction
to derived restriction of scalars along the structure homomorphism at `U'`. -/
def structureBaseChange : StructureBaseChange F O O' φ where
  baseChange U' := dBaseChange.{r, max u v u' v'} (φ.app U') (hO _) (hO' _)
  adj U' := dBaseChangeAdj.{r, max u v u' v'} (φ.app U') (hO _) (hO' _)

/-- **Derived pullback along a morphism of ringed topoi carries cartesian objects to cartesian
objects**, the derived base changes along the structure homomorphisms of `g` being the ones
constructed here and the cartesian condition on either side being taken with respect to an
arbitrary base-change datum — which by `isQC_iff_of_baseChangeData` is no choice at all. -/
theorem isQC_Lpullback_of_structureBaseChange
    (bc : BaseChangeData.{max u' v'} O) (bc' : BaseChangeData.{max u v} O')
    (d : DerivedPullbackData (structureBaseChange F O O' φ hO hO') bc bc')
    (K : DMod.{max u' v'} O) (hK : IsQC.{max u' v'} bc K) :
    IsQC.{max u v} bc' (d.Lpullback.obj K) :=
  isQC_Lpullback d K hK

/-- **Stacks 0GZ1.** **Derived pullback along a morphism of ringed topoi carries cartesian
objects to cartesian objects.** If the derived sections of `K` are cartesian then so are the
derived sections of `Lg^*K`, the cartesian condition on either side being taken with respect to
the derived base changes along the restriction homomorphisms of the structure sheaf there.

The derived pullback is supplied as data, together with the computation of its derived sections
of Stacks 0D6D, in the same way that
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.MorphismOfSites` supplies it for the
statements of Stacks 0H0R and 0H0S. -/
@[stacks 0GZ1 "pullback of cartesian objects, for a derived pullback with its sections"]
theorem isQC_Lpullback_of_comm
    (d : DerivedPullbackData (structureBaseChange F O O' φ hO hO')
      (baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
      (baseChangeDataOfComm.{r, v', u', max u v} O' hO'))
    (K : DMod.{max u' v'} O)
    (hK : IsQC.{max u' v'} (baseChangeDataOfComm.{r, v, u, max u' v'} O hO) K) :
    IsQC.{max u v} (baseChangeDataOfComm.{r, v', u', max u v} O' hO') (d.Lpullback.obj K) :=
  isQC_Lpullback d K hK

/-- The functor `QC(O) ⥤ QC(O')` through which a derived pullback along `g` factors, the full
subcategories of objects with cartesian derived sections being stable under `Lg^*`. -/
def qcPullbackOfComm
    (d : DerivedPullbackData (structureBaseChange F O O' φ hO hO')
      (baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
      (baseChangeDataOfComm.{r, v', u', max u v} O' hO')) :
    QC.{max u' v'} (baseChangeDataOfComm.{r, v, u, max u' v'} O hO) ⥤
      QC.{max u v} (baseChangeDataOfComm.{r, v', u', max u v} O' hO') :=
  qcPullback d

end Setting

end Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

end
