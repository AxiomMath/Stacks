module

public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Rig.FiniteTypeCompletions
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
public import StacksFrontier.RingTheory.Rig.RigEtaleOverAdicCompletion
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic
import all StacksFrontier.RingTheory.Rig.RigEtaleOverAdicCompletion

/-!
# The completion of a finite type algebra étale off `V(I)` is a rig-étale arrow

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `C` a finite type `A`-algebra with
`Spec C → Spec A` étale over `Spec A ∖ V(I)`. Part (1) of Stacks 0ALQ says that the `I`-adic
completion `C^` is rig-étale over `(A, I)`. This file turns that into the statement that the
completed map `A^ → C^` is a rig-étale arrow of `WAdm^{Noeth}` (Definition 0GCV): it is adic of
topologically finite type and makes `C^` rig-étale over `(A^, IA^)`. This is the translation the
proof of Stacks 0AR2 (and of Stacks 0GDH) performs on each affine chart.

## Main results

* `Rig.isRigEtale_adicCompletion_of_isRigEtale`: rig-étaleness over `(R, I)` implies
  rig-étaleness over `(R^∧, IR^∧)`, the converse of `Rig.isRigEtale_of_isRigEtale_adicCompletion`.
* `Rig.isRigEtaleHom_completionMap_of_isEtaleOutside`: the completed map `A^ → C^` of a finite
  type algebra étale off `V(I)` is continuous and a rig-étale arrow of `WAdm^{Noeth}`.

## Implementation notes

The passage from `(R, I)` to `(R^∧, IR^∧)` reads both conditions through condition (4) of
Stacks 0AJU, as in `Rig.isRigEtale_of_isRigEtale_adicCompletion`: on the finite levels
`R ⧸ Iⁿ = R^∧ ⧸ IⁿR^∧`. The only new point is that condition (4) over `R^∧` quantifies over all
elements of `(IR^∧)^c`, not only over images of elements of `I^c`; but the elements of `R^∧`
annihilating the relevant homology form an ideal, which contains the image of `I^c` and hence the
ideal `(IR^∧)^c` it generates.

## References

* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u

/-- **Rig-étaleness ascends to the completion of the base.** Let `R` be a Noetherian ring,
`I ⊆ R` an ideal and `A = R^∧` its `I`-adic completion. An `A`-algebra `C`, viewed over `R`
through `R → A`, which is rig-étale over `(R, I)` is rig-étale over `(A, IA)`: both conditions
are condition (4) of Stacks 0AJU, read on the finite levels `R ⧸ Iⁿ = A ⧸ IⁿA`. -/
public theorem isRigEtale_adicCompletion_of_isRigEtale
    {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C]
    (I : Ideal R) [Algebra (AdicCompletion I R) C] [Algebra R C]
    [IsScalarTower R (AdicCompletion I R) C]
    (hc : IsAdicComplete (I.map (algebraMap R C)) C)
    [Algebra.FiniteType (R ⧸ I) (C ⧸ I.map (algebraMap R C))]
    (hc' : IsAdicComplete
      ((I.map (algebraMap R (AdicCompletion I R))).map
        (algebraMap (AdicCompletion I R) C)) C)
    [Algebra.FiniteType (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)))
      (C ⧸ (I.map (algebraMap R (AdicCompletion I R))).map
        (algebraMap (AdicCompletion I R) C))]
    (h : IsRigEtale (AdicFiniteTypeAlgebra.of (I := I) C hc)) :
    IsRigEtale (AdicFiniteTypeAlgebra.of
      (I := I.map (algebraMap R (AdicCompletion I R))) C hc') := by
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let B := AdicFiniteTypeAlgebra.of (I := I) C hc
  let B' := AdicFiniteTypeAlgebra.of (I := J) C hc'
  let P := completedPolynomialPresentation I I.fg_of_isNoetherianRing B
  let P' := completedPolynomialPresentation J J.fg_of_isNoetherianRing B'
  obtain ⟨c, hc⟩ := ((tfae_isRigEtale B P).out 1 4).mp h
  apply ((tfae_isRigEtale B' P').out 1 4).mpr
  refine ⟨c, fun n hn a ha ↦ ?_⟩
  have hJ : J ^ n = (I ^ n).map (algebraMap R A) :=
    (Ideal.map_pow (algebraMap R A) I n).symm
  have hbijAux (J' : Ideal A) (hJ' : J' = (I ^ n).map (algebraMap R A)) :
      Function.Bijective (Ideal.quotientMap J' (algebraMap R A)
        (hJ' ▸ Ideal.le_comap_map)) := by
    subst J'
    exact bijective_quotientMap_pow_adicCompletion I I.fg_of_isNoetherianRing n
  have hbij := hbijAux (J ^ n) hJ
  -- the elements of `A` annihilating both homology modules form an ideal
  let ψ : A →+* C ⧸ (J ^ n).map (algebraMap A C) :=
    (Ideal.Quotient.mk _).comp (algebraMap A C)
  let K : Ideal A :=
    (Module.annihilator (C ⧸ (J ^ n).map (algebraMap A C))
        ((Algebra.naiveCotangentComplex (A ⧸ J ^ n)
          (C ⧸ (J ^ n).map (algebraMap A C))).homology 1)).comap ψ ⊓
      (Module.annihilator (C ⧸ (J ^ n).map (algebraMap A C))
        ((Algebra.naiveCotangentComplex (A ⧸ J ^ n)
          (C ⧸ (J ^ n).map (algebraMap A C))).homology 0)).comap ψ
  have hle : J ^ c ≤ K := by
    show (I.map (algebraMap R A)) ^ c ≤ K
    rw [← Ideal.map_pow]
    refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_
    have hr' := hc n hn r hr
    exact ⟨(mem_annihilator_homology_quotient_iff (C := C) (I ^ n) (J ^ n) hJ hbij 1 r).mp hr'.1,
      (mem_annihilator_homology_quotient_iff (C := C) (I ^ n) (J ^ n) hJ hbij 0 r).mp hr'.2⟩
  exact hle ha

/-- The image of `IB` under an `A`-algebra map `g : B → C` is `IC`. -/
private theorem map_map_algebraMap_algHom {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] (g : B →ₐ[A] C) (I : Ideal A) :
    (I.map (algebraMap A B)).map g.toRingHom = I.map (algebraMap A C) := by
  rw [Ideal.map_map, show g.toRingHom.comp (algebraMap A B) = algebraMap A C from
    RingHom.ext g.commutes]

/-- If `A ⧸ I → C ⧸ IC` is of finite type, then so is `B ⧸ IB → C ⧸ IC` for any `A`-algebra
map `g : B → C`. -/
private theorem finiteType_quotientMap_map_algHom {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] (g : B →ₐ[A] C) (I : Ideal A)
    (h : (Ideal.quotientMap (I.map (algebraMap A C)) (algebraMap A C)
      Ideal.le_comap_map).FiniteType) :
    (Ideal.quotientMap ((I.map (algebraMap A B)).map g.toRingHom) g.toRingHom
      Ideal.le_comap_map).FiniteType := by
  have hmap := map_map_algebraMap_algHom g I
  have hfin₀ : ∀ (K : Ideal C) (_ : I.map (algebraMap A C) = K)
      (h' : I ≤ K.comap (algebraMap A C)),
      (Ideal.quotientMap K (algebraMap A C) h').FiniteType := by
    rintro _ rfl _
    exact h
  have hI : I ≤ ((I.map (algebraMap A B)).map g.toRingHom).comap (algebraMap A C) := by
    rw [hmap]
    exact Ideal.le_comap_map
  have hcomp : (Ideal.quotientMap ((I.map (algebraMap A B)).map g.toRingHom) g.toRingHom
      Ideal.le_comap_map).comp (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map) =
      Ideal.quotientMap ((I.map (algebraMap A B)).map g.toRingHom) (algebraMap A C) hI := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    exact congrArg (Ideal.Quotient.mk _) (g.commutes a)
  exact RingHom.FiniteType.of_comp_finiteType (hcomp ▸ hfin₀ _ hmap.symm hI)

/-- **The completed map of a finite type algebra étale off `V(I)` is a rig-étale arrow.** Let
`A` be a Noetherian ring, `I ⊆ A` an ideal and `C` a finite type `A`-algebra étale over
`Spec A ∖ V(I)`. Give `A^ = A^∧_I` and `C^ = C^∧_{IC}` topologies in which they are adic rings,
defined by `IA^` and by `IC^`. Then the completed map `A^ → C^` is continuous and rig-étale in
the sense of Definition 0GCV.

It is adic of topologically finite type by Stacks 0GBW, `A^ ⧸ IA^ = A ⧸ I → C^ ⧸ IC^` being of
finite type; and `C^` is rig-étale over `(A^, IA^)` because it is rig-étale over `(A, I)` by
part (1) of Stacks 0ALQ (`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`). -/
public theorem isRigEtaleHom_completionMap_of_isEtaleOutside {A C : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C] (I : Ideal A)
    (hEt : IsEtaleOutside I C)
    [TopologicalSpace (AdicCompletion I A)] [IsTopologicalRing (AdicCompletion I A)]
    [TopologicalSpace (AdicCompletion (I.map (algebraMap A C)) C)]
    [IsTopologicalRing (AdicCompletion (I.map (algebraMap A C)) C)]
    (hAadic : _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))))
    (hCadic : _root_.IsAdic ((I.map (algebraMap A C)).map
      (algebraMap C (AdicCompletion (I.map (algebraMap A C)) C))))
    (hA : TopologicalRing.IsAdic (AdicCompletion I A))
    (hC : TopologicalRing.IsAdic (AdicCompletion (I.map (algebraMap A C)) C)) :
    Continuous (AdicCompletion.completionMap (B := C) I) ∧
      RingHom.IsRigEtaleArrow (AdicCompletion.completionMap (B := C) I).toRingHom := by
  let Â := AdicCompletion I A
  let Ĉ := AdicCompletion (I.map (algebraMap A C)) C
  let g := AdicCompletion.completionMap (B := C) I
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let J := I.map (algebraMap A Â)
  have hmapA : J.map g.toRingHom = I.map (algebraMap A Ĉ) := map_map_algebraMap_algHom g I
  have hmap : J.map g.toRingHom = (I.map (algebraMap A C)).map (algebraMap C Ĉ) :=
    hmapA.trans (map_map_algebraMap_algHom (IsScalarTower.toAlgHom A C Ĉ) I).symm
  have hcont : Continuous g := continuous_of_isAdic_of_map_le hAadic hCadic g.toRingHom hmap.le
  refine ⟨hcont, ?_⟩
  intro _ _ _ _
  have hJdef : TopologicalRing.IsIdealOfDefinition J :=
    TopologicalRing.isIdealOfDefinition_of_isAdic hAadic
  -- `A ⧸ I → C^ ⧸ IC^` is of finite type, hence so is `A^ ⧸ IA^ → C^ ⧸ IC^`
  have hfinJ : (Ideal.quotientMap (J.map g.toRingHom) g.toRingHom Ideal.le_comap_map).FiniteType :=
    finiteType_quotientMap_map_algHom g I
      (RingHom.finiteType_algebraMap.mpr (adicCompletion_finiteType_quotient A I C))
  have h3 : FiniteTypeModuloSomeIdealOfDefinition g.toRingHom :=
    ⟨⟨J, hJdef, hmap ▸ hCadic⟩, ⟨J, hJdef, hfinJ⟩⟩
  have hft : FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom :=
    ((adicFiniteType_tfae g.toRingHom hcont hA hC ⟨J, hJdef, I.fg_of_isNoetherianRing.map _⟩
      ⟨_, TopologicalRing.isIdealOfDefinition_of_isAdic hCadic,
        (I.map (algebraMap A C)).fg_of_isNoetherianRing.map _⟩).out 3 6).mp h3
  refine ⟨hcont, hft, J, hJdef, ?_⟩
  -- rig-étaleness over `(A^, IA^)`, from rig-étaleness over `(A, I)`
  let : Algebra Â Ĉ := g.toRingHom.toAlgebra
  have : IsScalarTower A Â Ĉ := IsScalarTower.of_algebraMap_eq fun a ↦ (g.commutes a).symm
  have hc : IsAdicComplete (I.map (algebraMap A Ĉ)) Ĉ := adicCompletion_isAdicallyComplete A I C
  have : Algebra.FiniteType (A ⧸ I) (Ĉ ⧸ I.map (algebraMap A Ĉ)) :=
    adicCompletion_finiteType_quotient A I C
  have hc' : IsAdicComplete (J.map (algebraMap Â Ĉ)) Ĉ := by
    show IsAdicComplete (J.map g.toRingHom) Ĉ
    rw [hmapA]
    exact hc
  have hfJ : Algebra.FiniteType (Â ⧸ J) (Ĉ ⧸ J.map (algebraMap Â Ĉ)) :=
    RingHom.finiteType_algebraMap.mp hfinJ
  have h0 : IsRigEtale (AdicFiniteTypeAlgebra.of (I := I) Ĉ hc) := by
    have heq : AdicFiniteTypeAlgebra.of (I := I) Ĉ hc = adicCompletionObj I (B := C) :=
      ObjectProperty.FullSubcategory.ext rfl
    rw [heq]
    exact isRigEtale_adicCompletionObj_of_isEtaleOutside I hEt
  exact ⟨hc', hfJ, isRigEtale_adicCompletion_of_isRigEtale I hc hc' h0⟩

end Rig

end
