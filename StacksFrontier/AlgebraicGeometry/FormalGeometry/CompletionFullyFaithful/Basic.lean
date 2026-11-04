module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.AlgebraicGeometry.QuasiAffine
import all StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sectionwise criteria for full faithfulness of the completion functor

Let `Y ⊆ X` be a closed subscheme of a Noetherian scheme, cut out by a quasi-coherent ideal
sheaf `I`, and let `Y_n ⊆ X` be the infinitesimal neighbourhoods of `Y`. Stacks 0EKP compares
four conditions:

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` carries an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})`
   is an isomorphism for all `m ≫ 0`;
3. `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism for every finite locally free module `ℰ`;
4. the completion functor `Coh(𝒪_X) → Coh(X, I)` of Stacks 0880 is fully faithful on the full
   subcategory of finite locally free objects,

and asserts (1) ⇒ (2) ⇒ (3) ⇒ (4) and (4) ⇒ (3).

This file states the comparison against the library's own vocabulary and proves the first
implication, together with the three general results it factors through. The isomorphism in
(1)–(3) is expressed, as in the formal statement of Stacks 0EJZ, by the universal
property of the inverse limit: every compatible family of sections on the infinitesimal
neighbourhoods has a unique antecedent in `Γ(X, ℰ)`. The index `n` of
`nthInfinitesimalNeighbourhood` is the source's `n + 1`, so the family swept out is exactly the
source's `Y_1, Y_2, …`; the limit is unchanged because the index set is cofinal.

## Main definitions

* `Stacks.Algebraization.nthInfinitesimalNeighbourhood` and
  `Stacks.Algebraization.nthInfinitesimalNeighbourhoodι` — the closed subscheme of the canonical
  open neighbourhood of an immersion cut out by the `(n+1)`-st power of its ideal sheaf, and its
  structure morphism to the ambient scheme. These are the objects of Stacks 04EY; no attribute is
  placed here, since that tag's covering set is a chapter-26 matter and larger than this.
* `Stacks.Algebraization.IsInfinitesimalSectionsComplete` — conditions (1)–(3) above, for a fixed
  module.
* `Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree` — condition (4), as
  bijectivity of the completion map on each hom set between finite locally free coherent sheaves.

## Main results

* `AlgebraicGeometry.pullbackGlobalSections_natural` and
  `AlgebraicGeometry.pullbackSectionsMap_natural` — the two canonical maps on global sections
  along a morphism of schemes are natural in the module. Neither direction of naturality was
  available: both maps were built from the unit of the pullback–pushforward adjunction and only
  their functoriality in the *morphism* had been recorded.
* `Stacks.SheafOfModules.Invertible.tensorPowerUnitIso` — every natural tensor power of the
  structure sheaf is again the structure sheaf.
* `AlgebraicGeometry.Scheme.Modules.isAmple_unit_of_isQuasiAffine` and
  `AlgebraicGeometry.Scheme.Modules.isQuasiAffine_of_isAmple_unit`, assembled as
  `AlgebraicGeometry.Scheme.Modules.isQuasiAffine_iff_isAmple_unit` — **Stacks 01QE**: a scheme
  is quasi-affine if and only if `𝒪_X` is ample. Only the first direction is used by Tag 0EKP.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_iso` — section completeness depends
  only on the isomorphism class of the module.
* `Stacks.Algebraization.quasiAffine_sectionsComplete_implies_amplePower_sectionsComplete` —
  **Stacks 0EKP, (1) implies (2)**.

## Implementation notes

The source proves (1) ⇒ (2) in one sentence: on a quasi-affine scheme `𝒪_X` is ample by
Properties, Lemma 01QE, so `L = 𝒪_X` works. Two things have to be supplied to make that a proof
here. First 01QE itself, whose Stacks proof goes through `Spec(A) = Proj(A[T])`; the direction
needed is instead immediate from `AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`,
which says that the *affine* basic opens of global functions form a basis, since the definition of
ampleness used in this library asks exactly for an affine nonvanishing locus of a section of a
positive tensor power through every point. The converse direction reads that same correspondence
backwards: an affine nonvanishing locus of a section of `𝒪_X^{⊗ n}` becomes an affine basic open
of a global function once the power is identified with `𝒪_X` by `tensorPowerUnitIso` and the locus
is identified with a basic open by
`Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen`, so the two clauses of ampleness are
exactly the hypotheses of `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`
and the source's detour through `Proj` is not needed in either direction.
Secondly the eventual-powers clause of (2) is about
`L^{⊗ m}`, not about `L`, so it needs `tensorPowerUnitIso` — obtained from the successor
comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n+1)}` and the right unit constraint of the sheaf tensor product
by induction — together with the invariance of section completeness under isomorphism, which is
where the two naturality lemmas are consumed.

Three crossings of the kind this area is full of had to be handled without relaxing
definitional-equality transparency. `rw` cannot cross the semireducible projection separating
`Γ(F, U)` from a presheaf's sections, so the naturality lemmas and the invariance proof are in
term mode throughout, using `Eq.trans`/`congrArg` and the elementwise `NatTrans.naturality_apply`
of `Scheme.Modules.Hom.mapPresheaf` in place of a rewrite. `(nthInfinitesimalNeighbourhoodOver i
n).hom` and `nthInfinitesimalNeighbourhoodι i n` are definitionally but not syntactically equal,
which is a second reason `rw` fails there. And `SheafOfModules.unit X.ringCatSheaf`,
`SheafOfModules.unit (structureSheafRing
  X.toRingedSpace)` and
`SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  X.toRingedSpace.presheaf _)` are three spellings
of one object for which invertibility is found at only one; the instance is therefore supplied
positionally, at each spelling that is needed.

## Where the other three implications are

All three are now carried, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/Chain.lean`, which also
states Tag 0EKP in full and carries its attribute:
`Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers` is
(2) ⇒ (3), `completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree` is (3) ⇒ (4) and
`sectionsCompleteFiniteLocallyFree_of_completionFullyFaithful` is (4) ⇒ (3). The implication
(1) ⇒ (2) proved below is quoted there as the first link of the chain, so the attribute is not
placed on it: the covering set of the tag is the one declaration stating all four implications.

The inputs catalogued here as missing have since been supplied:
`Stacks.Algebraization.exists_dual_embedding` builds the universally exact sequence of (2) ⇒ (3)
out of clause (8) of Tag 01Q3,
`Stacks.Algebraization.isInfinitesimalSectionsComplete_of_sectionsKernel` and
`isInfinitesimalSectionsComplete_bicone_pt` give the stability of
`IsInfinitesimalSectionsComplete` under a kernel and under finite biproducts,
`Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent` gives that
`SheafHom` of two finite locally free modules is finite locally free, and
`Stacks.Algebraization.isIso_globalSectionsToLimit_iff_isInfinitesimalSectionsComplete` is the
comparison between the two presentations of the inverse limit that (3) ⇔ (4) rests on.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Naturality of `pullbackGlobalSections` in the module. -/
public theorem pullbackGlobalSections_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    pullbackGlobalSections f N (φ.app ⊤ s) =
      ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackGlobalSections f M s) :=
  let hop := (eqToHom (show (⊤ : X.Opens) = f ⁻¹ᵁ (⊤ : Y.Opens) by simp)).op
  let b := fun u => ((Scheme.Modules.pullback f).obj N).presheaf.map hop u
  ((NatTrans.naturality_apply ((Scheme.Modules.pullback f).map φ).mapPresheaf hop
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ s)).trans
    (congrArg b (Stacks.Divisors.pullbackGlobalSections_naturality f φ s))).symm

private lemma sectionMorphism_natural {S : Scheme.{u}} {M N : S.Modules} (φ : M ⟶ N)
    {A B : Over S} (g : A ⟶ B) :
    (Scheme.Modules.pullback B.hom).map φ ≫ sectionMorphism N g =
      sectionMorphism M g ≫ (Scheme.Modules.pushforward g.left).map
        ((Scheme.Modules.pullback A.hom).map φ) := by
  unfold sectionMorphism
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.naturality
    ((Scheme.Modules.pullback B.hom).map φ)
  have hc := (Scheme.Modules.pullbackComp g.left B.hom).hom.naturality φ
  have hd := (Scheme.Modules.pullbackCongr (Over.w g)).hom.naturality φ
  simp only [Functor.comp_map, Functor.id_map] at hu hc hd
  rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← Functor.map_comp]
  congr 1
  rw [← Category.assoc, hc, Category.assoc, hd, ← Functor.map_comp, Category.assoc]

/-- Naturality of `pullbackSectionsMap` in the module. -/
public theorem pullbackSectionsMap_natural {S : Scheme.{u}} {M N : S.Modules} (φ : M ⟶ N)
    {A B : Over S} (g : A ⟶ B) (s : Γ((Scheme.Modules.pullback B.hom).obj M, ⊤)) :
    pullbackSectionsMap N g (((Scheme.Modules.pullback B.hom).map φ).app ⊤ s) =
      ((Scheme.Modules.pullback A.hom).map φ).app ⊤ (pullbackSectionsMap M g s) := by
  rw [pullbackSectionsMap_eq, pullbackSectionsMap_eq]
  have key := congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ s) (sectionMorphism_natural φ g)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app] at key
  let hop := (eqToHom (show (⊤ : A.left.Opens) = g.left ⁻¹ᵁ (⊤ : B.left.Opens) by simp)).op
  exact (congrArg (fun u => ((Scheme.Modules.pullback A.hom).obj N).presheaf.map hop u) key).trans
    (NatTrans.naturality_apply ((Scheme.Modules.pullback A.hom).map φ).mapPresheaf hop
      (Scheme.Modules.Hom.app (sectionMorphism M g) ⊤ s)).symm

end AlgebraicGeometry

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Every natural tensor power of the structure sheaf is again the structure sheaf. -/
public noncomputable def tensorPowerUnitIso
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))]
        :
    (n : ℕ) →
      tensorPower O hO (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (n : ℤ) ≅
        _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
  | 0 => Iso.refl _
  | n + 1 =>
      (tensorPowerReindex O hO _ (by push_cast; ring :
          ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).symm ≪≫
        (tensorPowerSuccIso O hO _ (n : ℤ)).symm ≪≫
          tensorProductRightUnitor O hO _ ≪≫ tensorPowerUnitIso n

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- **Stacks 01QE**, the direction `𝒪_X` ample implies `X` quasi-affine. -/
public theorem isQuasiAffine_of_isAmple_unit (Y : Scheme.{u})
    (h : IsAmple Y (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))) :
    Y.IsQuasiAffine := by
  have : CompactSpace Y := h.1
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Y fun x => ?_
  obtain ⟨n, -, s, hxs, haff⟩ := h.2 x
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        Y.toRingedSpace.presheaf
        (structureSheafRing Y.toRingedSpace).property)) :=
    isInvertible_unit Y
  have e := @tensorPowerUnitIso _ _ _ Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property _ _ hinv n
  have h3 : (Y.toRingedSpace.basicOpen (U := ⊤)
        ((SheafOfModules.sectionsMap e.hom s).eval (op ⊤)) : Set Y.carrier)
      = nonvanishingLocus (X := Y.toLocallyRingedSpace.toRingedSpace)
          (tensorPower Y.toRingedSpace.presheaf
            (structureSheafRing Y.toRingedSpace).property
            (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) (n : ℤ)) s :=
    (nonvanishingLocus_unit_eq_basicOpen Y.toRingedSpace
      (SheafOfModules.sectionsMap e.hom s)).symm.trans
      (nonvanishingLocus_sectionsMap Y.toRingedSpace e s)
  refine ⟨(SheafOfModules.sectionsMap e.hom s).eval (op ⊤), ?_, h3.ge hxs⟩
  convert haff using 1
  exact TopologicalSpace.Opens.ext h3

/-- **Stacks 01QE**, the direction used by Tag 0EKP. -/
public theorem isAmple_unit_of_isQuasiAffine (Y : Scheme.{u}) [Y.IsQuasiAffine] :
    IsAmple Y (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) := by
  refine ⟨inferInstance, fun x => ⟨1, le_refl 1, ?_⟩⟩
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen Y).exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  have e := tensorPowerOneIso Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
  have htop := sectionsOfTop_eval_top
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) r
  have h := (nonvanishingLocus_sectionsMap Y.toRingedSpace e.symm
      (sectionsOfTop (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) r)).trans
    ((nonvanishingLocus_unit_eq_basicOpen Y.toRingedSpace
        (sectionsOfTop (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) r)).trans
      (congrArg (fun m => (Y.toRingedSpace.basicOpen m : Set Y.carrier)) htop))
  refine ⟨SheafOfModules.sectionsMap e.symm.hom
      (sectionsOfTop (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) r),
    h.ge hxr, ?_⟩
  convert hr using 1
  exact TopologicalSpace.Opens.ext h

/-- **Stacks 01QE.** A scheme is quasi-affine precisely when its structure sheaf, viewed as a
module over itself, is ample. -/
@[ega "II 5.1.2" "b ⇔ c′", ega "II 5.1.5" "Case L = O_X"]
public theorem isQuasiAffine_iff_isAmple_unit (Y : Scheme.{u}) :
    Y.IsQuasiAffine ↔
      IsAmple Y (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :=
  ⟨fun _ => isAmple_unit_of_isQuasiAffine Y, isQuasiAffine_of_isAmple_unit Y⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Algebraization

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The `n`-th infinitesimal neighbourhood of an immersion. -/
public noncomputable def nthInfinitesimalNeighbourhood (n : ℕ) : Scheme.{u} :=
  (i.liftCoborder.ker ^ (n + 1)).subscheme

/-- The structure morphism from the `n`-th infinitesimal neighbourhood to the ambient scheme. -/
public noncomputable def nthInfinitesimalNeighbourhoodι (n : ℕ) :
    nthInfinitesimalNeighbourhood i n ⟶ X :=
  (i.liftCoborder.ker ^ (n + 1)).subschemeι ≫ i.coborderRange.ι

/-- The `n`-th infinitesimal neighbourhood as a scheme over the ambient scheme. -/
public noncomputable abbrev nthInfinitesimalNeighbourhoodOver (n : ℕ) : Over X :=
  Over.mk (nthInfinitesimalNeighbourhoodι i n)

/-- The canonical inclusion of a smaller infinitesimal neighbourhood into a larger one. -/
public noncomputable def nthInfinitesimalNeighbourhoodTransition {n m : ℕ} (h : n ≤ m) :
    nthInfinitesimalNeighbourhoodOver i n ⟶ nthInfinitesimalNeighbourhoodOver i m :=
  Over.homMk
    (Scheme.IdealSheafData.inclusion
      (show i.liftCoborder.ker ^ (m + 1) ≤ i.liftCoborder.ker ^ (n + 1) from
        Scheme.IdealSheafData.le_def.mpr
          (fun U => Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))))
    (by
      simp [nthInfinitesimalNeighbourhoodOver, nthInfinitesimalNeighbourhoodι,
        nthInfinitesimalNeighbourhood, ← Category.assoc])

/-- Global sections of `F` are the inverse limit of the sections of its restrictions to the
infinitesimal neighbourhoods of the immersion. -/
public def IsInfinitesimalSectionsComplete (F : X.Modules) : Prop :=
  ∀ s : ∀ n : ℕ,
      Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F, ⊤),
    (∀ (n m : ℕ) (h : n ≤ m),
      pullbackSectionsMap F (nthInfinitesimalNeighbourhoodTransition i h) (s m) = s n) →
    ∃! t : Γ(F, ⊤), ∀ n : ℕ,
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F t = s n

private lemma app_hom_inv {F G : X.Modules} (e : F ≅ G) (y : Γ(G, ⊤)) :
    e.hom.app ⊤ (e.inv.app ⊤ y) = y :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ y) e.inv_hom_id

private lemma app_map_inv_hom {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules} (e : F ≅ G)
    (x : Γ((Scheme.Modules.pullback g).obj G, ⊤)) :
    ((Scheme.Modules.pullback g).map e.hom).app ⊤
        (((Scheme.Modules.pullback g).map e.inv).app ⊤ x) = x :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ x)
    (((Scheme.Modules.pullback g).mapIso e).inv_hom_id)

/-- Infinitesimal section completeness only depends on the isomorphism class of the module. -/
public theorem isInfinitesimalSectionsComplete_of_iso {F G : X.Modules} (e : F ≅ G)
    (h : IsInfinitesimalSectionsComplete i F) : IsInfinitesimalSectionsComplete i G := by
  intro s hs
  obtain ⟨t, ht, htuniq⟩ := h
    (fun n => ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).map e.inv).app ⊤
      (s n))
    (fun n m hnm =>
      (pullbackSectionsMap_natural e.inv
          (nthInfinitesimalNeighbourhoodTransition i hnm) (s m)).trans
        (congrArg _ (hs n m hnm)))
  refine ⟨e.hom.app ⊤ t, fun n => ?_, fun y hy => ?_⟩
  · exact (pullbackGlobalSections_natural _ e.hom t).trans
      ((congrArg _ (ht n)).trans (app_map_inv_hom _ e (s n)))
  · exact (app_hom_inv e y).symm.trans
      (congrArg _ (htuniq _ fun n =>
        (pullbackGlobalSections_natural _ e.inv y).trans (congrArg _ (hy n))))

/-- Completion along `I` is fully faithful on finite locally free coherent sheaves. -/
public abbrev CompletionFullyFaithfulOnFiniteLocallyFree
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData) : Prop :=
  ∀ F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F.obj →
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G.obj →
    Function.Bijective (fun f : F ⟶ G => (completionFunctor X I).map f)

/-- **Stacks 0EKP, (1) implies (2).** On a quasi-affine scheme the structure sheaf is itself an
ample invertible module, and every tensor power of it is again the structure sheaf, so section
completeness on the infinitesimal neighbourhoods transports to all powers. -/
@[stacks 0EKP "(1) implies (2)"]
public theorem quasiAffine_sectionsComplete_implies_amplePower_sectionsComplete
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (hX : Scheme.IsQuasiAffine X)
    (h : IsInfinitesimalSectionsComplete i (SheafOfModules.unit X.ringCatSheaf)) :
    ∃ (L : X.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L),
      letI := hL
      AlgebraicGeometry.Scheme.Modules.IsAmple X L ∧
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
          IsInfinitesimalSectionsComplete i
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (m : ℤ)) := by
  have := hX
  have h1 : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_unit X
  have h2 : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property)) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_unit X
  refine ⟨SheafOfModules.unit X.ringCatSheaf, h1, ?_, 0, fun m _ => ?_⟩
  · exact AlgebraicGeometry.Scheme.Modules.isAmple_unit_of_isQuasiAffine X
  · exact isInfinitesimalSectionsComplete_of_iso i
      (Stacks.SheafOfModules.Invertible.tensorPowerUnitIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property m).symm h

end Stacks.Algebraization

end
