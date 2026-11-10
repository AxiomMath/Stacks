module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Tensoring a quasi-isomorphism of K-flat complexes, above the ring universe

Let `R` be a commutative ring whose modules are allowed to inhabit a universe `max u v`
independent of the universe `u` of `R` itself. Tensoring a quasi-isomorphism between K-flat
complexes with an arbitrary complex again gives a quasi-isomorphism, so the tensor-total functor
attached to a K-flat complex inverts quasi-isomorphisms and therefore descends through the
localization. The resulting endofunctor of the derived category does not depend on the K-flat
resolution chosen, and it is exact.

## Main results

* `CochainComplex.DerivedTensor.quasiIso_tleftCochain_map`: a quasi-isomorphism between K-flat
  complexes stays a quasi-isomorphism after tensoring on the left with any complex.
* `CochainComplex.DerivedTensor.derivedTensorProduct`: the derived tensor product with a fixed
  object of the derived category, built from a K-flat resolution of any representative.
* `CochainComplex.DerivedTensor.derivedTensorProduct_commShift` and
  `…_isTriangulated`: it commutes with the shifts and is exact.
* `CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution`: any K-flat
  resolution of any representative computes it, by a comparison uniquely determined by its
  pullback to the homotopy category.
* `CochainComplex.DerivedTensor.tensorFlipIso`, `…_naturality`,
  `CochainComplex.DerivedTensor.quasiIso_tright_map` and
  `CochainComplex.DerivedTensor.quasiIso_tleft_map_of_kFlat`: the comparison between tensoring on
  the left and on the right, and preservation of quasi-isomorphisms by either version when the
  fixed factor is K-flat. These are the shared form of the flip argument; other sections of the
  chapter need them, so they are public here rather than duplicated there.

## Implementation notes

K-flatness here is the central `CochainComplex.KFlat` of
`StacksFrontier.Algebra.Homology.KFlat`, which is stated at a module universe `max u v`
independent of the ring's, against the lifted tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse`. Taking `v := u` recovers the
same-universe reading of these results directly, with no bridge and no second predicate.

These four results are kept apart from the symmetric derived tensor bifunctor of
`StacksFrontier.Homology.Tor.DerivedTensor`, which is stated for modules in the ring's own universe
and never refers to them. Separating them keeps the large-universe tensor instances out of that
file's elaboration, where the extra instance candidates make its coherence proofs very much more
expensive without changing what they say.

## References

* [The Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [The Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

open CategoryTheory

universe u v w

namespace CochainComplex.DerivedTensor

-- Mathlib's monoidal structure on `ModuleCat` requires the module universe to equal the ring's.
-- Instance search reaches it first and then fails trying to unify `max u v =?= u`, which Lean does
-- not treat as "does not apply", so it does not fall through to the lifted structure. Making the
-- lifted tensor product a local instance settles the choice for this file, and the tensor product
-- of complexes and `Tright` then elaborate against the structure these statements are about.
attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive


/-! ### Tensoring a quasi-isomorphism between K-flat complexes -/

section TensorQuasiIso

open MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

/-- Flipping the two factors of the tensor-product double complex, degreewise by the symmetry of
the tensor product of modules. This is the bicomplex-level ingredient of `tensorFlipIso`; it is
public only because that definition names it. -/
public noncomputable def tensorBicomplexFlipIso {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (((curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L ≅
    (((curriedTensor (ModuleCat.{max u v} R)).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => (TensorProduct.comm R (K.X p) (L.X q)).toModuleIso)
      (by intros; ext : 1; apply TensorProduct.ext'; intros; rfl))
    (by intros; ext q : 2; apply TensorProduct.ext'; intros; rfl)

/-- Tensoring on the left with `K` agrees with tensoring on the right with `K`, after totalizing:
the comparison is the flip of the double complex followed by Mathlib's flip isomorphism for
total complexes. -/
public noncomputable def tensorFlipIso {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (TleftCochain K).obj L ≅ (TrightCochain K).obj L :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexFlipIso K L) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K
      (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)

/-- `tensorFlipIso` is natural in the varying factor: it is an isomorphism of functors, not
merely an isomorphism at each object. -/
public lemma tensorFlipIso_naturality {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {A B : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : A ⟶ B) :
    (TleftCochain K).map f ≫ (tensorFlipIso K B).hom =
      (tensorFlipIso K A).hom ≫ (TrightCochain K).map f := by
  let F := curriedTensor (ModuleCat.{max u v} R)
  have h : (((F.mapBifunctorHomologicalComplex _ _).obj K).map f) ≫
        (tensorBicomplexFlipIso K B).hom =
      (tensorBicomplexFlipIso K A).hom ≫
        (((F.flip.mapBifunctorHomologicalComplex _ _).obj K).map f) := by
    ext p q : 3
    apply TensorProduct.ext'
    intros
    rfl
  have ht := congrArg (fun g => HomologicalComplex₂.total.map g (ComplexShape.up ℤ)) h
  change mapBifunctorMap (𝟙 K) f F _ ≫
      (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K B).hom _ ≫
        (mapBifunctorFlipIso B K F _).hom) =
    (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K A).hom _ ≫
      (mapBifunctorFlipIso A K F _).hom) ≫ mapBifunctorMap f (𝟙 K) F _
  rw [← Category.assoc]
  simp only [mapBifunctorMap]
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← HomologicalComplex₂.total.map_comp, ht]
  rw [HomologicalComplex₂.total.map_comp]
  simp only [Category.assoc]
  have hf := mapBifunctorFlipIso_hom_naturality f (𝟙 K) F (ComplexShape.up ℤ)
  have hf' :
      HomologicalComplex₂.total.map
          (((F.flip.mapBifunctorHomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map f) (ComplexShape.up ℤ) ≫
        (mapBifunctorFlipIso B K F (ComplexShape.up ℤ)).hom =
      (mapBifunctorFlipIso A K F (ComplexShape.up ℤ)).hom ≫
        HomologicalComplex₂.total.map
          (((F.mapBifunctorHomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app K) (ComplexShape.up ℤ) := by
    simpa [mapBifunctorMap] using hf
  rw [hf']

/-- Tensoring on the right with a K-flat complex preserves quasi-isomorphisms. This is the
cochain-level form of `CochainComplex.KFlat.kFlat_tright_preserves_quasiIso`, obtained by
transporting that statement across the quotient to the homotopy category. -/
public theorem quasiIso_tright_map {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : K.KFlat)
    {A B : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((TrightCochain K).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹QuasiIso f›
  have h := (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK)
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright K).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

/-- Tensoring on the *left* with a K-flat complex preserves quasi-isomorphisms. This is
`quasiIso_tright_map` transported across `tensorFlipIso`, and it is the form other sections of the
chapter need; it differs from `quasiIso_tleftCochain_map` below in requiring the fixed factor to be
K-flat rather than the two varying ones. -/
public theorem quasiIso_tleft_map_of_kFlat {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : K.KFlat)
    {A B : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((TleftCochain K).map f) := by
  have hr : QuasiIso ((TrightCochain K).map f) := quasiIso_tright_map K hK f
  have heq : (TleftCochain K).map f ≫ (tensorFlipIso K B).hom =
      (tensorFlipIso K A).hom ≫ (TrightCochain K).map f :=
    tensorFlipIso_naturality K f
  have hβA : QuasiIso (tensorFlipIso K A).hom := quasiIso_of_isIso _
  have hβB : QuasiIso (tensorFlipIso K B).hom := quasiIso_of_isIso _
  have hc : QuasiIso ((TleftCochain K).map f ≫ (tensorFlipIso K B).hom) := by
    rw [heq]
    exact quasiIso_comp (hφ := hβA) (hφ' := hr) _ _
  exact (quasiIso_iff_comp_right (hφ' := hβB) _ _).1 hc

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism after tensoring on
the left with any complex and taking the total complex. -/
@[stacks 064L]
public theorem quasiIso_tleftCochain_map {R : Type u} [CommRing R]
    {P Q : CochainComplex (ModuleCat.{max u v} R) ℤ} (α : P ⟶ Q) [QuasiIso α]
    (hP : P.KFlat) (hQ : Q.KFlat) (L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    QuasiIso ((TleftCochain L).map α) := by
  obtain ⟨K, r, hK, _, hr, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution L
  have : QuasiIso r := hr
  have hsquare : (TleftCochain K).map α ≫ (TrightCochain Q).map r =
      (TrightCochain P).map r ≫ (TleftCochain L).map α :=
    ((curriedTensor (ModuleCat.{max u v} R)).map₂CochainComplex.map r).naturality α
  have hcomp : QuasiIso ((TrightCochain P).map r ≫ (TleftCochain L).map α) := by
    rw [← hsquare]
    exact quasiIso_comp (hφ := quasiIso_tleft_map_of_kFlat K hK α)
      (hφ' := quasiIso_tright_map Q hQ r) _ _
  exact (quasiIso_iff_comp_left (hφ := quasiIso_tright_map P hP r) _ _).1 hcomp

end TensorQuasiIso

end CochainComplex.DerivedTensor

end
