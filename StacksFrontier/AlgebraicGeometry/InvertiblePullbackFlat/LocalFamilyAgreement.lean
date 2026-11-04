module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FamilyDescent
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyCover
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierAgreement
import StacksCore.Tactic.StacksAttribute

/-!
# The agreement hypothesis of Tag 0BD7 for a family on maximal opens

`Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn` assembles
the family of the penultimate paragraph of [Stacks, Tag 0BD7] onto preimages, and the last of its
hypotheses that nothing discharged is `hagree`: two members generating at a common point of a
fibre generate at the same points of that fibre.

For a family whose members live on *arbitrary* opens `hagree` is false, as `LocalFamilyUnit.lean`
records: two members with one multiplier on nested opens have nested generating loci, which
differ along a fibre leaving the smaller open. What rules that out is
`Stacks.InvertiblePullback.IsMaximalPullMeromorphicFamilyOn`, the clause that `V i` is the
largest open of `φ^{-1}(A i)` on which `φ^*(g_i) s` is regular, which
`Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamilyOn` supplies. With it the
source's argument goes through: at the common point the two multipliers differ by a unit germ on
the base, hence by a unit section `w` on an open `B` of the base; the fibre lies in
`φ^{-1}(B)`; and on `φ^{-1}(B) ⊓ V j` the section `φ^*(w) t_j` represents `φ^*(g_i) s`, so
maximality puts that open inside `V i` and identifies `t_i` there with `φ^*(w) t_j`. A unit
multiple has the same generating locus, which is the agreement asked for.

## Main results

* `Stacks.InvertiblePullback.mem_generatingLocus_of_restrictₛₗ_pullbackMeromorphicMul_eq_smul`:
  the agreement from a unit relation between the products on a preimage.
* `Stacks.InvertiblePullback.mem_generatingLocus_of_isMaximalPullMeromorphicFamilyOn`: the
  agreement in the one direction the argument proves, with the unit relation found.
* `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_isMaximalPullMeromorphicFamilyOn`:
  `hagree`, with nothing assumed of the family beyond the family equation and maximality.
* `Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamily`: the penultimate
  paragraph's family on the preimages, with `hex`, from the triviality of `ℒ` on the generic
  fibre alone — the hypothesis `hfam` of `FamilyDescent.lean`, discharged.
* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat`:
  **[Stacks, Tag 0BD7]** with no hypothesis the source does not have.

## Implementation notes

The relation between the multipliers is pulled back at the level of
`AlgebraicGeometry.meromorphicSectionSheafAsModule` rather than of `ℒ`, which is what makes the
argument work for a family on arbitrary opens:
`Stacks.InvertiblePullback.restrictₛₗ_eq_smul_of_isPullMeromorphicFamily` concludes about `t i`
and `t j` and so needs them defined on the whole preimage, while here only the *meromorphic*
product is restricted to the preimage and the regular section enters on `V j` alone.

`Stacks.InvertiblePullback.restrictₛₗ_app_smul` is applied to
`AlgebraicGeometry.meromorphicSectionSheafAsModule X L` and not to `ℒ`; it is stated for an
arbitrary sheaf of `𝒪_X`-modules, and the sheaf of meromorphic sections is one, by restriction of
scalars along `𝒪_X ⟶ 𝒦_X`.

The scalar `w` of the pushforward module structure and `(f.app B).hom w` of the structure sheaf
upstairs are the same by definition of that structure, which is the step
`Stacks.InvertiblePullback.restrictₛₗ_eq_smul_of_isPullMeromorphicFamily` also takes; the two
spellings are therefore related by a `have` with a declared type and not by a rewrite.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L)
    {ι : Type*} {A : ι → Y.Opens} {V : ι → Opens X.toRingedSpace.carrier}
    (hVA : ∀ i, (V i : X.Opens) ≤ (f ⁻¹ᵁ A i : X.Opens))
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op (V i)))

/-- Restricting a meromorphic section twice is restricting along the composite. -/
private theorem restrictₛₗ_restrictₛₗ_meromorphic
    {U₁ U₂ U₃ : Opens X.toRingedSpace.carrier} (h1 : U₂ ≤ U₁) (h2 : U₃ ≤ U₂) (h3 : U₃ ≤ U₁)
    (m : (meromorphicSectionSheafAsModule X L).val.obj (op U₁)) :
    (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE h2).op
        ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE h1).op m)
      = (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE h3).op m :=
  ((meromorphicSectionSheafAsModule X L).val.map_comp_apply
      (homOfLE h1).op (homOfLE h2).op m).symm.trans
    ((meromorphicSectionSheafAsModule X L).val.congr_map_apply (Subsingleton.elim _ _) m)

include hVA in
/-- **The agreement clause from a unit relation between the products on a preimage.** If the
meromorphic products `φ^*(g_i) s` and `φ^*(g_j) s` differ on `φ^{-1}(B)` by a unit of `𝒪_X`
there, then at every point of `φ^{-1}(B)` at which `t j` generates, `t i` generates too.

Maximality of `V i` is what does the work. The unit multiple of `t j` on `φ^{-1}(B) ⊓ V j` is a
regular section representing `φ^*(g_i) s` there, so that open lies in `V i` and `t i` is that
multiple on it; and a unit multiple has the same generating locus
(`Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul`). Note that `z` is not
assumed to lie in `V i`: that it does is part of the conclusion. -/
theorem mem_generatingLocus_of_restrictₛₗ_pullbackMeromorphicMul_eq_smul
    [IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L]
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (hmax : IsMaximalPullMeromorphicFamilyOn f L s g t)
    (i j : ι) {B : Y.Opens}
    (hpBi : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A i : X.Opens))
    (hpBj : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A j : X.Opens))
    (c : X.toRingedSpace.presheaf.obj
      (op ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hcu : IsUnit c)
    (hrel : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hpBi).op
          ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
        = HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
              (J := Opens.grothendieckTopology X) X.sheaf).obj.obj
              (op ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier))))
            c ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hpBj).op
              ((pullbackMeromorphicMul f L s).val.app (op (A j)) (g j))))
    (z : X.toRingedSpace.carrier) (hzB : f.base z ∈ B)
    (hzj : z ∈ generatingLocus L (t j)) :
    z ∈ generatingLocus L (t i) := by
  set W : Opens X.toRingedSpace.carrier :=
    ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ⊓ V j with hWdef
  have hWB : W ≤ ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) := inf_le_left
  have hWVj : W ≤ V j := inf_le_right
  have hWi : W ≤ ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier) := hWB.trans hpBi
  have hcWu : IsUnit (X.toRingedSpace.presheaf.map (homOfLE hWB).op c) :=
    hcu.map (ConcreteCategory.hom (X.toRingedSpace.presheaf.map (homOfLE hWB).op))
  have hstep : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hWi).op
        ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
      = HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op W)))
          (X.toRingedSpace.presheaf.map (homOfLE hWB).op c)
          ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ
            (homOfLE (hWVj.trans (hVA j))).op
            ((pullbackMeromorphicMul f L s).val.app (op (A j)) (g j))) :=
    (restrictₛₗ_restrictₛₗ_meromorphic L hpBi hWB hWi _).symm.trans
      ((congrArg (fun m => (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
            (homOfLE hWB).op m) hrel).trans
        ((((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hWB).op).map_smulₛₗ
            c _).trans
          (congrArg (fun m => HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
              (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op W)))
              (X.toRingedSpace.presheaf.map (homOfLE hWB).op c) m)
            (restrictₛₗ_restrictₛₗ_meromorphic L hpBj hWB (hWVj.trans (hVA j)) _))))
  have htj : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
        (homOfLE (hWVj.trans (hVA j))).op
        ((pullbackMeromorphicMul f L s).val.app (op (A j)) (g j))
      = (toMeromorphicSectionSheafAsModule X L).val.app (op W)
          (L.val.restrictₛₗ (homOfLE hWVj).op (t j)) :=
    (restrictₛₗ_restrictₛₗ_meromorphic L (hVA j) hWVj (hWVj.trans (hVA j)) _).symm.trans
      ((congrArg (fun m => (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
          (homOfLE hWVj).op m) (ht j)).trans
        (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
          (homOfLE hWVj).op (t j)).symm)
  obtain ⟨hWVi, hti⟩ := hmax i W hWi _
    (hstep.trans ((congrArg (fun m => HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op W)))
          (X.toRingedSpace.presheaf.map (homOfLE hWB).op c) m) htj).trans
      (LinearMap.map_smul ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom
        (X.toRingedSpace.presheaf.map (homOfLE hWB).op c)
        (L.val.restrictₛₗ (homOfLE hWVj).op (t j))).symm))
  exact (mem_generatingLocus_iff_of_restrictₛₗ_eq_smul L hWVi hWVj hcWu hti
    ⟨hzB, generatingLocus_le L (t j) hzj⟩).mpr hzj

include hVA in
/-- **The agreement clause of [Stacks, Tag 0BD7] for a family on maximal opens.** If `t i` and
`t j` both generate at `x` and `t j` generates at a point `z` of the fibre through `x`, then
`t i` generates at `z` too.

This is the half of `hagree` that carries content; the other half is this one with `i` and `j`
exchanged. The unit relating the two multipliers is found at `x` — on the intersection of the two
generating loci upstairs, then as a germ on the base, then as a section on an open `B` of the
base — and the fibre through `x` lies in `φ^{-1}(B)`, which is what carries the conclusion to
every point of it. -/
theorem mem_generatingLocus_of_isMaximalPullMeromorphicFamilyOn
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L]
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (hmax : IsMaximalPullMeromorphicFamilyOn f L s g t)
    (i j : ι) (x : X.toRingedSpace.carrier)
    (hxi : x ∈ generatingLocus L (t i)) (hxj : x ∈ generatingLocus L (t j))
    (z : X.toRingedSpace.carrier) (hz : f.base z = f.base x)
    (hzj : z ∈ generatingLocus L (t j)) :
    z ∈ generatingLocus L (t i) := by
  classical
  set W : Opens X.toRingedSpace.carrier :=
    ⟨_, isOpen_inter_generatingLocus L (t i) (t j)⟩ with hWdef
  have hxW : x ∈ W := ⟨hxi, hxj⟩
  have hWi : W ≤ V i := fun y hy => generatingLocus_le L (t i) hy.1
  have hWj : W ≤ V j := fun y hy => generatingLocus_le L (t j) hy.2
  obtain ⟨c, hcu, hc⟩ := exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus L (t i) (t j)
    hWi hWj (fun _ hy => hy.1) (fun _ hy => hy.2)
  have hxi' : f.base x ∈ A i := hVA i (hWi hxW)
  have hxj' : f.base x ∈ A j := hVA j (hWj hxW)
  obtain ⟨v, hv, hgerm⟩ := exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamilyOn f L s hVA g t
    hs ht i j hxW hWi hWj c hcu hc hxi' hxj'
  obtain ⟨A', hyA', hA'i, hA'j, w, hwu, hw⟩ :=
    exists_isUnit_germ_restrictₛₗ_eq_smul_of_germ_eq_mul (f.base x) hxi' hxj' (g i) (g j) v hv
      hgerm
  obtain ⟨B, hBA', hyB, hwB⟩ := exists_le_isUnit_res_of_isUnit_germ (f.base x) hyA' w hwu
  have hpi : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A i : X.Opens) :=
    fun y hy => hA'i hy
  have hpj : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A j : X.Opens) :=
    fun y hy => hA'j hy
  have hpB : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A' : X.Opens) :=
    fun y hy => hBA' hy
  have hrel : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hpi).op
        ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
      = HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf).obj.obj
            (op ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier))))
          ((f.app A').hom w)
          ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hpj).op
            ((pullbackMeromorphicMul f L s).val.app (op (A j)) (g j))) :=
    restrictₛₗ_pullbackMeromorphicMul_eq_smul f L s (g i) (g j) hA'i hA'j w hw
  have hrelB : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
        (homOfLE (hpB.trans hpi)).op ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
      = HSMul.hSMul (α := ((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf).obj.obj
            (op ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier))))
          ((f.app B).hom (Y.presheaf.map (homOfLE hBA').op w))
          ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hpB.trans hpj)).op
            ((pullbackMeromorphicMul f L s).val.app (op (A j)) (g j))) :=
    (restrictₛₗ_restrictₛₗ_meromorphic L hpi hpB (hpB.trans hpi) _).symm.trans
      ((congrArg (fun m => (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
          (homOfLE hpB).op m) hrel).trans
        (restrictₛₗ_app_smul f (meromorphicSectionSheafAsModule X L) hBA' w hpB hpj _))
  refine mem_generatingLocus_of_restrictₛₗ_pullbackMeromorphicMul_eq_smul f L s hVA g t ht hmax
    i j (hpB.trans hpi) (hpB.trans hpj) _ (hwB.map (f.app B).hom) hrelB z ?_ hzj
  rw [hz]
  exact hyB

include hVA in
/-- **The agreement hypothesis `hagree` of [Stacks, Tag 0BD7], discharged.** Nothing is assumed of
the family but the family equation and the maximality of its opens, both of which
`Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamilyOn` produces. -/
theorem forall_mem_generatingLocus_iff_of_isMaximalPullMeromorphicFamilyOn
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L]
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (hmax : IsMaximalPullMeromorphicFamilyOn f L s g t) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)) :=
  fun i j x hxi hxj z hz =>
    ⟨fun h => mem_generatingLocus_of_isMaximalPullMeromorphicFamilyOn f L s hVA g t hs ht hmax
        j i x hxj hxi z hz h,
      fun h => mem_generatingLocus_of_isMaximalPullMeromorphicFamilyOn f L s hVA g t hs ht hmax
        i j x hxi hxj z hz h⟩

section Cover

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (L : X.Modules) [L.IsQuasicoherent]
    (hL : IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L)
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
    (hfib : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))

include hL hgen hfib in
/-- **The penultimate paragraph of [Stacks, Tag 0BD7], on the preimages.** The family of
meromorphic multipliers is produced by
`Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamilyOn` on maximal opens, its
agreement property comes from that maximality, and the saturation argument of the last paragraph
then puts each member on a whole preimage.

This is the conjunction the hypothesis `hfam` of
`Stacks.InvertiblePullback`'s
`exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section` asks for. -/
theorem exists_span_eq_top_isPullMeromorphicFamily
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    letI : Module (ringStalk X.toRingedSpace (genericPoint X))
        (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
      stalkModule X.toRingedSpace L.val (genericPoint X)
    ∃ (m : grpStalk X.toRingedSpace L.val (genericPoint X)) (A : Y → Y.Opens)
      (g : ∀ y, (totalQuotientSheafAsModule Y).val.obj (op (A y)))
      (t : ∀ y, L.val.obj (op ((f ⁻¹ᵁ A y : X.Opens) : Opens X.toRingedSpace.carrier))),
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤ ∧
        IsPullMeromorphicFamily f L (meromorphicSectionOfGenericStalk X L m) g t ∧
          ∀ z : X.toRingedSpace.carrier, ∃ y, z ∈ generatingLocus L (t y) := by
  have : IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L := hL
  have hne : ∀ y : Y, Nonempty (f.fiber y) := fun y => (hfib y).nonempty
  have hsurj : Function.Surjective f.base := (Surjective.of_nonempty_fiber f hne).surj
  have hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}) := by
    intro y
    have := hfib y
    exact isIrreducible_preimage_singleton_of_isIntegral_fiber f y
  obtain ⟨m, A, V, hVA, q, t, hspan, hfam, hmax, hgL⟩ :=
    exists_span_eq_top_isPullMeromorphicFamilyOn f L hL hgen hfib hsurj
  have hs := AlgebraicGeometry.isRegularMeromorphicSection_of_span_eq_top_grpStalk X L m hspan
  obtain ⟨A', g', t', hfam', hex'⟩ :=
    exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn f L
      (meromorphicSectionOfGenericStalk X L m) hVA q t hfam (fun z => ⟨z, hgL z⟩) hirr
      (forall_mem_generatingLocus_iff_of_isMaximalPullMeromorphicFamilyOn f L
        (meromorphicSectionOfGenericStalk X L m) hVA q t hs hfam hmax) hne hfinite
  exact ⟨m, A', g', t', hspan, hfam', hex'⟩

end Cover

section Descent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (L : X.Modules)

/-- **Stacks Project, Tag 0BD7.** Let `φ : X ⟶ Y` be a morphism of schemes and `ℒ` an invertible
`𝒪_X`-module. Assume `X` is locally Noetherian, `Y` is locally Noetherian, integral and normal,
`φ` is flat with integral fibres, `φ` is quasi-compact or locally of finite type, and `ℒ` is
trivial on the generic fibre of `φ`. Then `ℒ ≅ φ^*𝒩` for an invertible `𝒪_Y`-module `𝒩`.

The family of meromorphic multipliers of the penultimate paragraph of the source's proof is no
longer a hypothesis: it is
`Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamily`.

Invertibility of `ℒ` is the hypothesis `hL` alone: the class instance that
`FamilyDescent.lean` carries beside it is the same statement in another spelling and is
obtained from `hL` inside the proof, so no hypothesis here is absent from
[Stacks, Tag 0BD7]. -/
@[stacks 0BD7]
theorem exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (hfibre : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    (hgeneric : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) := by
  have : IsInvertible X.presheaf (_root_.structureSheafRing X.toRingedSpace).property L := hL
  refine exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section f L hL
    hfibre hfinite hgeneric ?_
  intro _
  have : AlgebraicGeometry.IsIntegral (f.fiber (genericPoint Y)) := hfibre (genericPoint Y)
  have : AlgebraicGeometry.IsIntegral X := isIntegral_of_flat_of_isIntegral_genericFiber f
  have : L.IsQuasicoherent := Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L
  obtain ⟨m, A, g, t, hspan, hfam, hex⟩ :=
    exists_span_eq_top_isPullMeromorphicFamily f L ‹_› hgeneric hfibre hfinite
  exact ⟨m, Y, A, g, t, hspan, hfam, hex⟩

end Descent

end Stacks.InvertiblePullback

end
