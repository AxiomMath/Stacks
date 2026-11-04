module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationTor
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChange
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Triangle
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatResolution
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The general form of Tag 0F7X at the ring level

`StacksFrontier.Homology.Eta.Perfect.GoodBaseChange` builds the comparison chain map
`B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)` and proves Tag 0F7X at the particular presentation
`P = η_f C`. This file proves the *general* form of the tag: the one in which the presentation
of `η_f 𝒦` is an arbitrary K-flat complex `P`, and in which flatness of `B` over `A` is
replaced by goodness — the hypothesis that `𝒦` has a presentation by a bounded complex `C` of
finite free `A`-modules all of whose determinantal ideals `I_i(C, f)` are principal.

The ingredients, which `GoodBaseChange` names but does not prove, are

* `B ⊗_A -` carries a quasi-isomorphism between K-flat complexes to a quasi-isomorphism;
* `B ⊗_A -` carries a homotopy to a homotopy;
* `η_f C` is K-projective, so that `η_f ψ` lifts through `p : P ⟶ η_f 𝒦` up to homotopy; and
* `η_f C` and `C` are themselves K-flat, so that the first item applies to the lift and to `ψ`.

## Main results

* `Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat`:
  **Tag 0F7X at the ring level, in its general form.** For an arbitrary ring map `A → B` — no
  flatness — and a K-flat presentation `p : P ⟶ η_f 𝒦` of the décalage of a K-flat complex `𝒦`
  of flat `A`-modules presented by a good bounded complex `C` of finite free modules, the
  composite `B ⊗_A P ⟶ B ⊗_A (η_f 𝒦) ⟶ η_g (B ⊗_A 𝒦)` is a quasi-isomorphism.
* `Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_of_kFlat`: **`B ⊗_A -` preserves
  quasi-isomorphisms between K-flat complexes.** No flatness of `B` over `A` and no
  boundedness is assumed; K-flatness of the two complexes is the whole hypothesis.
* `Stacks.Eta.GoodBaseChange.baseChangeHomotopy`: **`B ⊗_A -` preserves homotopies.**
* `Stacks.Eta.GoodBaseChange.isKProjective_etaObject_toCochainComplex`: **`η_f C` is
  K-projective.**
* `Stacks.Eta.GoodBaseChange.kFlat_etaObject_toCochainComplex`: **`η_f C` is K-flat.**
* `Stacks.Eta.GoodBaseChange.kFlat_toCochainComplex`: **a bounded complex of finite free
  modules is K-flat.**

## Main definitions

* `Stacks.Eta.GoodBaseChange.extendScalarsLargeNatIso`: the comparison of the two spellings of
  degreewise base change on complexes, `CochainComplex.extendScalarsLarge (algebraMap A B)` and
  the `baseChangeComplex` of `GoodBaseChange`.

## Implementation notes

**The two spellings of `B ⊗_A -`.** `Stacks.Eta.GoodBaseChange.baseChangeComplex` is built
from `B ⊗[A] -` for the ambient `Algebra A B` instance, so that it matches
`Stacks.Eta.BaseChange` verbatim, whereas the K-flatness apparatus of
`StacksDraft.Homology.KFlat` is written for `ModuleCat.extendScalars`, which forms `B ⊗_A M`
with the `A`-module structure `Module.compHom B (algebraMap A B)` on `B`. Those two module
structures agree but not definitionally, so the two tensor products are not the same term.
The reconciliation is already in the tree and is an *equality of functors*,
`Stacks.extendScalars_eq_algebraBaseChange`: `ModuleCat.extendScalars (algebraMap A B)` is
`Stacks.algebraBaseChange A B`, the degreewise `M ↦ B ⊗[A] M` for the algebra structure. So
nothing here is restated in a second spelling; instead

* `baseChangeComplex` and `baseChangeMap` are recognised as
  `(Stacks.algebraBaseChange A B).mapHomologicalComplex (ComplexShape.up ℤ)` on the nose
  (`algebraBaseChange_mapHomologicalComplex_obj` and `..._map`, both `rfl`), which is what makes
  the generic machinery for an additive functor on complexes — `Functor.mapHomotopy` and
  `CochainComplex.mappingCone.mapHomologicalComplexIso` — apply to it directly; and
* `extendScalarsLargeNatIso` transports the one statement that is available only for
  `extendScalars`, namely
  `CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic`.

**K-projectivity and K-flatness of `η_f C`.** Tag 0F7W
(`EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal`) makes each
term `(η_f C)^i` a finite projective `A`-module as soon as `I_i(C, f)` is principal
(`projective_etaObject_X`), and `η_f C` is bounded above because `C` is: in a degree where `C`
has rank `0` the localization `(C^i)_f` is already zero, so the décalage term inside it is
(`exists_isStrictlyLE_etaObject_toCochainComplex`). Those two facts give K-projectivity by
`CochainComplex.isKProjective_of_projective` and K-flatness by Stacks 064K in the form
`StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective`, which is also what makes `C`
itself K-flat, its terms being finite free.

The K-flatness statement here is `CochainComplex.KFlat`, acyclicity of `L ⊗ -` against every
acyclic `L` of `A`-modules. The sheaf-level `kFlat_of_isStrictlyPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat` is a
different predicate — `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X` on complexes
of `O_X`-modules — and does not apply.

**Preservation of quasi-isomorphisms.** A morphism is a quasi-isomorphism exactly when its
mapping cone is acyclic (`CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone`), and
the mapping cone of a morphism between K-flat complexes is K-flat, by the two-out-of-three
property of K-flatness in the distinguished mapping-cone triangle (Tag 06Y2,
`CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang`). An *acyclic* K-flat complex has
acyclic base change along an arbitrary ring map (Tag 06Y2's companion,
`CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic`), and base change
commutes with the mapping cone because it is additive. So no resolution, no flatness of `B` and
no boundedness enters; the hypothesis is exactly K-flatness of source and target, which is what
the consumer has.

**Where flatness of `B` over `A` would have been used, and what replaces it.** In the flat case
one gets `QuasiIso (B ⊗ ψ)` from `B ⊗ -` being exact. Here it comes instead from K-flatness of
`C` and of `𝒦`, and the passage from the presentation `η_f C` of `GoodBaseChange` to an
arbitrary K-flat presentation `P` is a lift–and–cancel argument: `η_f ψ` factors through
`p : P ⟶ η_f 𝒦` up to homotopy because `η_f C` is K-projective, the lift `β : η_f C ⟶ P` is a
quasi-isomorphism by two-out-of-three, its base change is one because `η_f C` and `P` are
K-flat, and cancelling it off the base-changed homotopy leaves exactly the conclusion.

## References

* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 06Y2](https://stacks.math.columbia.edu/tag/06Y2)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

namespace Stacks.Eta.GoodBaseChange

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## `baseChangeComplex` is the degreewise base-change functor on complexes -/

/-- Base change of modules along the structure map of an algebra is additive: it is Mathlib's
extension of scalars, by `Stacks.extendScalars_eq_algebraBaseChange`, and that is additive. -/
instance algebraBaseChange_additive : (Stacks.algebraBaseChange A B).Additive :=
  Stacks.extendScalars_eq_algebraBaseChange A B ▸
    (inferInstance : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive)

/-- The base-changed complex of `StacksFrontier.Homology.Eta.Perfect.GoodBaseChange` is the
degreewise base-change functor `Stacks.algebraBaseChange` applied to complexes. -/
theorem algebraBaseChange_mapHomologicalComplex_obj (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((Stacks.algebraBaseChange A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K =
      baseChangeComplex (B := B) K := rfl

/-- The base change of a map of complexes is the degreewise base-change functor on morphisms. -/
theorem algebraBaseChange_mapHomologicalComplex_map
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L) :
    ((Stacks.algebraBaseChange A B).mapHomologicalComplex (ComplexShape.up ℤ)).map φ =
      baseChangeMap (B := B) φ := rfl

/-- **The comparison of the two spellings of degreewise base change on complexes.**  Mathlib's
`CochainComplex.extendScalarsLarge` along `algebraMap A B` is the `baseChangeComplex` of
`StacksFrontier.Homology.Eta.Perfect.GoodBaseChange`, naturally in the complex. -/
def extendScalarsLargeNatIso :
    CochainComplex.extendScalarsLarge.{u, u, u} (algebraMap A B) ≅
      (Stacks.algebraBaseChange A B).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (Stacks.extendScalarsNatIso A B) (ComplexShape.up ℤ)

/-! ## `B ⊗_A -` preserves homotopies -/

/-- **`B ⊗_A -` preserves homotopies.**  A homotopy between two maps of complexes of
`A`-modules base-changes to a homotopy between the two base-changed maps. -/
def baseChangeHomotopy {K L : CochainComplex (ModuleCat.{u} A) ℤ} {φ ψ : K ⟶ L}
    (h : Homotopy φ ψ) :
    Homotopy (baseChangeMap (B := B) φ) (baseChangeMap (B := B) ψ) :=
  (Stacks.algebraBaseChange A B).mapHomotopy h

/-! ## `B ⊗_A -` preserves quasi-isomorphisms between K-flat complexes -/

/-- **`B ⊗_A -` preserves quasi-isomorphisms between K-flat complexes.**  Let `A → B` be any
map of commutative rings and let `φ : K ⟶ L` be a quasi-isomorphism of K-flat complexes of
`A`-modules.  Then `B ⊗_A φ` is a quasi-isomorphism.  Neither complex is assumed bounded, and
`B` is not assumed flat over `A`. -/
@[ega "III 6.10.3" "Remark 6.10.3(ii)"]
theorem quasiIso_baseChangeMap_of_kFlat {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L)
    (φ : K ⟶ L) (hφ : QuasiIso φ) :
    QuasiIso (baseChangeMap (B := B) φ) := by
  have hcone : CochainComplex.KFlat.{u, u} (CochainComplex.mappingCone φ) :=
    (CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang _ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ)).2.2 hK hL
  have hac : (CochainComplex.mappingCone φ).Acyclic :=
    (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone φ).1 hφ
  have h2 : (baseChangeComplex (B := B) (CochainComplex.mappingCone φ)).Acyclic :=
    HomologicalComplex.Acyclic.of_iso
      (extendScalarsLargeNatIso.app (CochainComplex.mappingCone φ))
      (CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic.{u, u, u}
        (algebraMap A B) hcone hac)
  refine (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).2 ?_
  exact HomologicalComplex.Acyclic.of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ (Stacks.algebraBaseChange A B)) h2

/-! ## `η_f C` is K-projective and K-flat -/

/-- **Every term of `η_f C` is a projective `A`-module**, by Tag 0F7W
(`EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal`): the degree-`i`
term of `η_f C` is the décalage term of the matrix of `d^i`, which is finite projective as soon
as `I_i(C, f)` is principal. -/
theorem projective_etaObject_X (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (i : ℤ) :
    Projective ((EtaComplex.etaObject f C.toCochainComplex).X i) := by
  have hterm : EtaComplex.term f C.toCochainComplex i =
      EtaPow.fetaTerm f (C.d i).mulVecLin i :=
    congrArg (fun m => EtaPow.fetaTerm f m i) (congrArg ModuleCat.Hom.hom (C.toCochainComplex_d i))
  obtain ⟨⟨_, hpr, _⟩, _⟩ :=
    EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf i (hI i)
  have hmod : Module.Projective A (EtaComplex.term f C.toCochainComplex i) := by
    rw [hterm]
    exact hpr
  show Projective (ModuleCat.of A (EtaComplex.term f C.toCochainComplex i))
  infer_instance

/-- **`η_f C` is strictly bounded above**, because `C` is: in a degree `i` where `C` has rank `0`
the term `(C)^i` is already zero, hence so is the localization `(C^i)_f` and so is the décalage
term sitting inside it. -/
theorem exists_isStrictlyLE_etaObject_toCochainComplex (C : BoundedComplex A) (f : A) :
    ∃ b : ℤ, (EtaComplex.etaObject f C.toCochainComplex).IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := C.bounded.bddAbove
  refine ⟨b, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hr : C.rank i = 0 := by_contra fun h => not_le_of_gt hi (hb h)
  have hsub : Subsingleton (C.toCochainComplex.X i) := by
    show Subsingleton (Fin (C.rank i) → A)
    rw [hr]
    infer_instance
  show IsZero (ModuleCat.of A (EtaComplex.term f C.toCochainComplex i))
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

/-- **`η_f C` is K-projective.**  Let `f ∈ A` be a nonzerodivisor and let `C` be a bounded
complex of finite free `A`-modules all of whose determinantal ideals `I_i(C, f)` are principal.
Then the décalage `η_f C` is a K-projective complex: each term is finite projective by
Tag 0F7W, and the complex is bounded above because `C` is. -/
theorem isKProjective_etaObject_toCochainComplex (C : BoundedComplex A) (f : A)
    (hf : IsRegular f) (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    (EtaComplex.etaObject f C.toCochainComplex).IsKProjective := by
  obtain ⟨b, hb⟩ := exists_isStrictlyLE_etaObject_toCochainComplex C f
  have := hb
  have := projective_etaObject_X C f hf hI
  exact CochainComplex.isKProjective_of_projective _ b

/-- **`η_f C` is K-flat.**  Same hypotheses as `isKProjective_etaObject_toCochainComplex`: the
complex is bounded above and its terms are projective, hence flat, so Stacks 064K
(`StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective`) applies. -/
theorem kFlat_etaObject_toCochainComplex (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    CochainComplex.KFlat.{u, u} (EtaComplex.etaObject f C.toCochainComplex) := by
  obtain ⟨b, hb⟩ := exists_isStrictlyLE_etaObject_toCochainComplex C f
  have := hb
  exact StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective _ b
    (projective_etaObject_X C f hf hI)

/-- **A bounded complex of finite free modules is K-flat.**  `C.toCochainComplex` is strictly
bounded above (`Stacks.Eta.DeterminantalIdeal.toCochainComplex_bounded`) and each of its terms
is a finite free, hence projective, `A`-module, so Stacks 064K applies. -/
theorem kFlat_toCochainComplex (C : BoundedComplex A) :
    CochainComplex.KFlat.{u, u} C.toCochainComplex := by
  obtain ⟨-, b, -, hb⟩ := Stacks.Eta.DeterminantalIdeal.toCochainComplex_bounded C
  have := hb
  refine StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective _ b fun i => ?_
  show Projective (ModuleCat.of A (Fin (C.rank i) → A))
  infer_instance

/-! ## The general form of Tag 0F7X at the ring level -/

/-- **Tag 0F7X at the ring level, in its general form.**  Let `A → B` be an arbitrary map of
commutative rings — `B` is *not* assumed flat over `A` — let `f ∈ A` be a nonzerodivisor whose
image `g` in `B` is a nonzerodivisor, and let `C` be a bounded complex of finite free
`A`-modules all of whose determinantal ideals `I_i(C, f)` are principal: the ring-level form of
*goodness*, which here replaces flatness of `B` over `A`.  Let `𝒦` be a K-flat complex of flat
`A`-modules receiving a quasi-isomorphism `ψ : C ⟶ 𝒦`, and let `p : P ⟶ η_f 𝒦` be a
quasi-isomorphism out of an arbitrary K-flat complex `P` of `A`-modules.  Then the composite

`B ⊗_A P ⟶ B ⊗_A (η_f 𝒦) ⟶ η_g (B ⊗_A 𝒦)`

is a quasi-isomorphism.

The proof: `C` and `𝒦` are K-flat, so `B ⊗ ψ` is a quasi-isomorphism and
`quasiIso_etaBaseChangeMap_comp_of_toCochainComplex` gives the statement at the particular
presentation `P = η_f C`, `p = η_f ψ`.  Since `η_f C` is K-projective, `η_f ψ` lifts through the
quasi-isomorphism `p` to some `β : η_f C ⟶ P` with `β ≫ p` homotopic to `η_f ψ`; as `η_f ψ` and
`p` are quasi-isomorphisms so is `β`, whence — `η_f C` and `P` both being K-flat — so is
`B ⊗ β`.  Base-changing the homotopy and cancelling `B ⊗ β` gives the conclusion. -/
theorem quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (hg : IsRegular (algebraMap A B f))
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal)
    (𝒦 : CochainComplex (ModuleCat.{u} A) ℤ) (h𝒦 : CochainComplex.KFlat.{u, u} 𝒦)
    (h𝒦flat : ∀ i : ℤ, Module.Flat A (𝒦.X i))
    (ψ : C.toCochainComplex ⟶ 𝒦) (hψ : QuasiIso ψ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (p : P ⟶ EtaComplex.etaObject f 𝒦) (hp : QuasiIso p) :
    QuasiIso (baseChangeMap (B := B) p ≫ etaBaseChangeMap (B := B) f 𝒦) := by
  have hfnzd : f ∈ nonZeroDivisors A := isRegular_iff_mem_nonZeroDivisors.mp hf
  have hcons : QuasiIso (baseChangeMap (B := B) (EtaComplex.etaMap f ψ) ≫
      etaBaseChangeMap (B := B) f 𝒦) :=
    quasiIso_etaBaseChangeMap_comp_of_toCochainComplex C f hf hg hI 𝒦 h𝒦flat ψ
      (quasiIso_baseChangeMap_of_kFlat (kFlat_toCochainComplex C) h𝒦 ψ hψ)
  have hetaψ : QuasiIso (EtaComplex.etaMap f ψ) :=
    quasiIso_etaMap f hfnzd
      (isTorsionFree_of_flat f hfnzd C.toCochainComplex fun i =>
        (inferInstance : Module.Flat A (Fin (C.rank i) → A)))
      (isTorsionFree_of_flat f hfnzd 𝒦 h𝒦flat) ψ hψ
  have := isKProjective_etaObject_toCochainComplex C f hf hI
  have := hp
  obtain ⟨β, ⟨hβ⟩⟩ :=
    (CochainComplex.IsKProjective.exists_lift_of_quasiIso p (EtaComplex.etaMap f ψ)).1
  have : QuasiIso (β ≫ p) :=
    (CochainComplex.DerivedTensor.quasiIso_congr_of_homotopy.{u, u} hβ).2 hetaψ
  have : QuasiIso β := quasiIso_of_comp_right β p
  have : QuasiIso (baseChangeMap (B := B) β) :=
    quasiIso_baseChangeMap_of_kFlat (kFlat_etaObject_toCochainComplex C f hf hI) hP β inferInstance
  have hmap : baseChangeMap (B := B) (β ≫ p) =
      baseChangeMap (B := B) β ≫ baseChangeMap (B := B) p :=
    ((Stacks.algebraBaseChange A B).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp β p
  have h3 : QuasiIso (baseChangeMap (B := B) (β ≫ p) ≫ etaBaseChangeMap (B := B) f 𝒦) :=
    (CochainComplex.DerivedTensor.quasiIso_congr_of_homotopy.{u, u}
      ((baseChangeHomotopy (B := B) hβ).compRight (etaBaseChangeMap (B := B) f 𝒦))).2 hcons
  rw [hmap, Category.assoc] at h3
  have := h3
  exact quasiIso_of_comp_left (baseChangeMap (B := B) β) _

end

end Stacks.Eta.GoodBaseChange

end
