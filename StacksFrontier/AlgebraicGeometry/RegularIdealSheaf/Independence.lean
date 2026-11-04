module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.QuasiRegular
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Independence of the chosen open in Stacks tag 063J

Stacks tag 063J calls an immersion `i : Z ⟶ X` *regular*, *Koszul-regular*, *`H₁`-regular* or
*quasi-regular* when the defining ideal sheaf of `Z` inside *some* open `U ⊆ X` in which `i` is
closed has the corresponding property of Stacks tag 063D, and asserts that the condition does not
depend on the choice of `U`.  This file proves that independence clause for the three conditions
of Stacks tag 063D that are local on the stalks — parts (2), (3) and (4), i.e. Koszul-regular,
`H₁`-regular and quasi-regular.

The chosen open enters a condition of Stacks tag 063D in exactly two ways: it is the space the
ideal sheaf lives on, and it bounds the neighbourhoods on which a generating sequence may be
produced.  The clause is therefore the conjunction of two statements, and both are proved here:

* the condition on `J|_V` over `X|_V` is a condition on the ambient `X`, namely that every point
  of `V` in the support of `O_X / J` has a generating sequence of the required kind on a
  neighbourhood contained in `V` (`isKoszulRegularIdealSheaf_restrictSubmodule_iff` and its two
  companions);
* that ambient condition is unchanged when `V` is replaced by any open cutting out the same part
  of the support (`isKoszulRegularIdealSheaf_restrictSubmodule_congr` and its two companions),
  because a witness may always be shrunk into a smaller open.

Two admissible opens for an immersion do cut out the same part of the support, since both contain
the image of `Z` and the support of the quotient meets the canonical open `i.coborderRange` only
in that image; so these statements are the independence clause.

## Main definitions

* `restrictSubmodule V J`: an ideal subsheaf of `O_X`, restricted to an open `V`, as an ideal
  subsheaf of `O_{X|_V}`.
* `imOpen V W`: an open of `X|_V`, read as an open of `X`.

## Main results

* `notMem_idealQuotientSupport_iff`: a point lies outside the support of `O_X / J` exactly when
  `J` contains the unit section over some open neighbourhood of it.  This is the key lemma: it
  turns the support — defined through the quotient sheaf, hence through a cokernel in
  `SheafOfModules` — into a condition on the sections of `J`, which restriction to an open
  manifestly preserves.
* `mem_idealQuotientSupport_restrictSubmodule_iff`: the support of the quotient is local.
* `isGeneratedByOn_restrictSubmodule_iff`, `isKoszulSequenceExactOn_restrict_iff`,
  `forall_isQuasiRegularRel_germFamily_restrict_iff`: generation by sections, Koszul exactness
  and the elementary relation condition are local.
* `isKoszulRegularIdealSheaf_restrictSubmodule_iff`, `isH1RegularIdealSheaf_restrictSubmodule_iff`
  and `isQuasiRegularIdealSheaf_restrictSubmodule_iff`: parts (2), (3) and (4) of Stacks tag 063D
  for a restricted ideal subsheaf, read on the ambient space.
* `isKoszulRegularIdealSheaf_restrictSubmodule_congr`,
  `isH1RegularIdealSheaf_restrictSubmodule_congr` and
  `isQuasiRegularIdealSheaf_restrictSubmodule_congr`: **the independence clause of Stacks tag
  063J**, parts (2), (3) and (4), for an ideal subsheaf on a ringed space and two opens cutting
  out the same part of the support.
* `mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom`: two opens in which an immersion
  is closed do cut out the same part of the support of the quotient by its defining ideal sheaf,
  which is what feeds the three statements above in the geometric situation.
* `isKoszulRegularIdealSheaf_definingIdealOfHom_congr`,
  `isH1RegularIdealSheaf_definingIdealOfHom_congr` and
  `isQuasiRegularIdealSheaf_definingIdealOfHom_congr`: **the independence clause for an
  immersion**, parts (2), (3) and (4): the condition on the restriction of `definingIdealOfHom i`
  to an open in which `i` is closed does not depend on that open.
* `restrictSubmodule_definingIdealOfHom`: the restriction to an open `V` of the defining ideal
  sheaf of `i` on the ambient `X` *is* the defining ideal sheaf of a factor `j : Z ⟶ V` of `i`.
* `isKoszulRegularImmersion_iff_of_open`, `isH1RegularImmersion_iff_of_open` and
  `isQuasiRegularImmersion_iff_of_open`: **the independence clause in the spelling Stacks tag
  063J uses**, parts (2), (3) and (4): an immersion satisfies the condition exactly when the
  defining ideal sheaf of its closed factor through *any* admissible open does.
* `isKoszulRegularIdealSheaf_restrictSubmodule_nested_iff`,
  `isH1RegularIdealSheaf_restrictSubmodule_nested_iff` and
  `isQuasiRegularIdealSheaf_restrictSubmodule_nested_iff`: **transport of the three conditions
  across the nesting isomorphism** `(X|_V)|_A ≅ X|_{imOpen V A}`, together with the
  ambient-space readings `isKoszulRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff`
  and companions they are deduced from.
* `restrictSubmodule_definingIdealOfHom_resLE`: the restriction to `V` of the defining ideal
  sheaf of `i` is the defining ideal sheaf of `i.resLE V (i ⁻¹ᵁ V) le_rfl`.
* `mem_coborderRange_resLE_iff` and `imOpen_coborderRange_resLE`: the canonical open of a
  restricted immersion is `V ⊓ i.coborderRange`.
* `isKoszulRegularImmersion_resLE`, `isH1RegularImmersion_resLE` and
  `isQuasiRegularImmersion_resLE`: **parts (2), (3) and (4) of Stacks tag 063J are stable under
  restricting the target to an open**, the clause the independence statement is used for
  downstream.

## Implementation notes

The support of `O_X / J` is `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp` of a cokernel in
`SheafOfModules`, about which nothing was known in this development.  It is computed here from
exactness of the stalk functor on sheaves of modules
(`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`): the stalk of the
quotient vanishes exactly when the stalk of `J` exhausts the stalk of `O_X`, and an ideal that
contains the unit germ already contains the unit section on a smaller open.

The conditions of Stacks tag 063D parts (2), (3) and (4) are conditions on the *germs* of a
generating sequence, and the stalks of `X|_V` at points of `V` are the stalks of `X` only up to
the canonical isomorphism `restrictStalkEquiv`.  Transporting the conditions along that
isomorphism needs them to be invariant under a ring isomorphism.  For the elementary relation
condition this is `isQuasiRegularRel_ringEquiv`; for Koszul homology it is proved here
(`koszulHomology_isZero_ringEquiv_iff`) from flat base change for the Koszul complex, Stacks tag
062H: a ring isomorphism is a flat ring map in both directions, and the Koszul complex with
coefficients in the base ring is the Koszul complex.

Part (1) of Stacks tag 063D, regularity, is stated as monicity of a multiplication morphism of
sheaves on `X|_U` rather than germwise, so it is not covered by the germ transport used here and
part (1) of the independence clause is not proved in this file.

The intermediate statements of this file spell the ideal sheaf on an admissible open `U` as
`restrictSubmodule U` of the defining ideal sheaf `definingIdealOfHom i` of `i` on the *ambient*
`X`, because restriction is what the locality arguments see.  The two spellings agree, and
`restrictSubmodule_definingIdealOfHom` proves it: identifying them means comparing
`i.app (U.ι ''ᵁ W)` with `j.app W`, whose targets are the sections of `O_Z` over two equal but
not syntactically identical opens of `Z` (`U.ι ⁻¹ᵁ (U.ι ''ᵁ W) = W` is
`Scheme.Hom.preimage_image_eq`, not `rfl`), so the comparison transports along that equality of
opens.  The same happens in `restrictSubmodule_definingIdealOfHom_resLE`, along
`image_preimage_resLE`.  These two `eqToHom`s are confined to those two proof bodies: no
`eqToHom` appears in the statement of any result of this file, tagged or not.  With them, the
independence clause is available in the Stacks spelling, as `isKoszulRegularImmersion_iff_of_open`
and its two companions.

Restricting the *target* of an immersion to an open `V` replaces the canonical open
`i.coborderRange` by `V ⊓ i.coborderRange`, and the ideal sheaf lives on a space
`(X|_V)|_A` that is not the restriction of `X` to any open — it is only isomorphic to
`X|_{imOpen V A}`.  The three conditions are transported across that isomorphism by reading
both sides on the ambient `X`: each of the three master statements of the previous section turns
the condition on a restriction into a condition on `X`, so applying it twice, once at each
level, identifies the two.  Concretely, the conditions are germwise, and
`isKoszulSequenceExactOn_restrict_iff`, `forall_isQuasiRegularRel_germFamily_restrict_iff` and
`mem_idealQuotientSupport_restrictSubmodule_iff` move the germ conditions point by point, which
is what makes the transport elementary; no comparison of sheaves across the isomorphism is ever
formed.

## References

* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 15.31.5 (Tag 062H)](https://stacks.math.columbia.edu/tag/062H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingTheory.QuasiRegular
open Stacks.RingTheory.RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### The support of the quotient, read off the sections of the ideal -/

section Support

variable {Y : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
  (J : (SheafOfModules.unit O).Submodule) (x : Y)

/-- The germ at `x` of a section of the structure sheaf, in the stalk of the unit module. -/
private noncomputable abbrev unitGerm (U : Opens Y) (hx : x ∈ U) (s : O.obj.obj (op U)) :
    AlgebraicGeometry.SheafOfModules.stalkObj O x (SheafOfModules.unit O) :=
  (TopCat.Presheaf.germ (SheafOfModules.unit O).val.presheaf U x hx).hom s

/-- The germ at `x` of a section of an ideal subsheaf, in the stalk of that subsheaf. -/
private noncomputable abbrev subGerm (U : Opens Y) (hx : x ∈ U)
    (s : (J.toSheafOfModules).val.obj (op U)) :
    AlgebraicGeometry.SheafOfModules.stalkObj O x (J.toSheafOfModules) :=
  (TopCat.Presheaf.germ (J.toSheafOfModules).val.presheaf U x hx).hom s

/-- **The stalk of an ideal subsheaf exhausts the stalk of the structure sheaf exactly when the
ideal contains the unit section near the point.** One direction shrinks the open on which a
section with germ `1` agrees with `1`; the other multiplies the germ of the unit section, which
lies in the image, by an arbitrary germ. -/
private theorem stalkMap_ι_surjective_iff :
    Function.Surjective (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom ↔
      ∃ U : Opens Y, ∃ _ : x ∈ U, (1 : O.obj.obj (op U)) ∈ J.obj (op U) := by
  constructor
  · intro hsurj
    obtain ⟨a, ha⟩ := hsurj (unitGerm x ⊤ trivial 1)
    obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq
      (J.toSheafOfModules).val.presheaf a
    subst ht
    have ha' : unitGerm x U hxU (J.ι.val.app (op U) t) = unitGerm x ⊤ trivial 1 :=
      (AlgebraicGeometry.SheafOfModules.stalkMap_germ O x J.ι U hxU t).symm.trans ha
    obtain ⟨W, hxW, iU, iTop, hW⟩ := TopCat.Presheaf.germ_eq
      (SheafOfModules.unit O).val.presheaf x hxU (show x ∈ (⊤ : Opens Y) from trivial)
      (J.ι.val.app (op U) t) (1 : O.obj.obj (op (⊤ : Opens Y))) ha'
    refine ⟨W, hxW, ?_⟩
    have h2 : ((SheafOfModules.unit O).val.presheaf.map iU.op).hom (J.ι.val.app (op U) t)
        ∈ J.obj (op W) := J.toSubmodule.map_mem iU.op t.2
    have hone : ((SheafOfModules.unit O).val.presheaf.map iTop.op).hom
        (1 : O.obj.obj (op (⊤ : Opens Y))) = (1 : O.obj.obj (op W)) :=
      map_one (O.obj.map iTop.op).hom
    exact (hW.trans hone) ▸ h2
  · rintro ⟨U, hxU, h1⟩
    intro b
    obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq
      (SheafOfModules.unit O).val.presheaf b
    have hxW : x ∈ V ⊓ U := ⟨hxV, hxU⟩
    have hle : V ⊓ U ≤ U := inf_le_right
    have h1W : (1 : O.obj.obj (op (V ⊓ U))) ∈ J.obj (op (V ⊓ U)) := by
      have h := J.toSubmodule.map_mem (homOfLE hle).op h1
      have hmo : (ConcreteCategory.hom ((SheafOfModules.unit O).val.map (homOfLE hle).op))
          (1 : O.obj.obj (op U)) = (1 : O.obj.obj (op (V ⊓ U))) :=
        map_one (O.obj.map (homOfLE hle).op).hom
      exact hmo ▸ h
    set r' : O.obj.obj (op (V ⊓ U)) :=
      (O.obj.map (homOfLE (inf_le_left (a := V) (b := U))).op).hom s with hr'
    refine ⟨(TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r' •
      subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩, ?_⟩
    calc (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom
          ((TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r' •
            subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩)
        = (TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r' •
            (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom
              (subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩) := map_smul _ _ _
      _ = (TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r' •
            unitGerm x (V ⊓ U) hxW (1 : O.obj.obj (op (V ⊓ U))) :=
            congrArg _ (AlgebraicGeometry.SheafOfModules.stalkMap_germ O x J.ι (V ⊓ U) hxW _)
      _ = unitGerm x (V ⊓ U) hxW (r' * (1 : O.obj.obj (op (V ⊓ U)))) :=
            (AlgebraicGeometry.SheafOfModules.germ_hom_smul O x (SheafOfModules.unit O).val
              (V ⊓ U) hxW r' (1 : O.obj.obj (op (V ⊓ U)))).symm
      _ = unitGerm x (V ⊓ U) hxW r' := by rw [mul_one]
      _ = unitGerm x V hxV s := TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit O).val.presheaf
            (homOfLE (inf_le_left (a := V) (b := U))) x hxW s
      _ = b := hs

/-- The quotient of the structure sheaf by an ideal subsheaf has zero stalk at `x` exactly when
the stalk of the ideal subsheaf is all of the stalk of the structure sheaf: the stalk functor on
sheaves of modules is exact, so it carries the short exact sequence of the quotient to a short
exact sequence of stalk modules. -/
private theorem stalk_cokernel_eq_zero_iff :
    (∀ a : (AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj
        (cokernel J.ι), a = 0) ↔
      Function.Surjective (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom := by
  have hse : ((ShortComplex.mk J.ι (cokernel.π J.ι) (cokernel.condition _)).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O x)).ShortExact := by
    refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).mp ?_ x
    exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel J.ι)
            mono_f := inferInstance
            epi_g := inferInstance }
  set S := (ShortComplex.mk J.ι (cokernel.π J.ι) (cokernel.condition _)).map
    (AlgebraicGeometry.SheafOfModules.stalkFunctor O x) with hS
  have hz : ∀ c : S.X₁, (ConcreteCategory.hom S.g) ((ConcreteCategory.hom S.f) c) = 0 := by
    intro c
    simp
  have hex := (ShortComplex.moduleCat_exact_iff _).mp hse.exact
  have hepi := hse.epi_g
  refine ⟨fun h b => hex b (h _), fun hsurj a => ?_⟩
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective _).mp hepi a
  obtain ⟨c, hc⟩ := hsurj b
  rw [← hb, ← hc]
  exact hz c

end Support

section SupportRingedSpace

variable {X : RingedSpace.{u}} (J : (structureSheafModule X).Submodule) (x : X)

/-- **The complement of the support of `O_X / J`, read off the sections of `J`.** A point is
outside the support of the quotient exactly when `J` contains the unit section over some open
neighbourhood of it, i.e. exactly when `J` agrees with `O_X` near the point.

This is the locality statement that the four conditions of Stacks tag 063D rest on: the
conditions quantify over the support of the quotient, and this identifies that support in terms
of the sections of `J` alone, with no reference to the quotient sheaf. -/
theorem notMem_idealQuotientSupport_iff :
    x ∉ idealQuotientSupport X J ↔
      ∃ U : Opens X, ∃ _ : x ∈ U, (1 : X.presheaf.obj (op U)) ∈ J.obj (op U) :=
  ((Iff.intro
      (fun (h : x ∉ idealQuotientSupport X J) a => by
        by_contra ha; exact h ⟨a, ha⟩)
      (fun h (hx : x ∈ idealQuotientSupport X J) => hx.elim fun a ha => ha (h a))) :
    x ∉ idealQuotientSupport X J ↔
      ∀ a : (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
        (cokernel (J : (structureSheafModule X).Submodule).ι), a = 0).trans
    ((stalk_cokernel_eq_zero_iff J x).trans (stalkMap_ι_surjective_iff J x))

/-- If `J` contains the unit section over an open neighbourhood of `x`, then `x` is not in the
support of `O_X / J`. -/
theorem notMem_idealQuotientSupport_of_one_mem (U : Opens X) (hxU : x ∈ U)
    (h1 : (1 : X.presheaf.obj (op U)) ∈ J.obj (op U)) : x ∉ idealQuotientSupport X J :=
  (notMem_idealQuotientSupport_iff J x).mpr ⟨U, hxU, h1⟩

end SupportRingedSpace


/-! ### Koszul homology under a ring isomorphism -/

section KoszulRingEquiv

open scoped TensorProduct

/-- **Koszul homology in a fixed degree transports along a ring isomorphism.** A ring
isomorphism is in particular a faithfully flat ring map, so this is flat base change for the
Koszul complex (Stacks tag 062H) with coefficients in the base ring, followed by the right
unitor on coefficients. -/
private theorem koszulHomology_isZero_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) {r : ℕ} (f : Fin r → R) (i : ℕ)
    (h : IsZero ((Koszul.seqComplex f).homology i)) :
    IsZero ((Koszul.seqComplex (fun k => e (f k))).homology i) := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have hsm : ∀ (c : R) (y : S), c • y = e c * y := fun c y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]; rfl
  let eL : R ≃ₗ[R] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun c y => by
        simp only [RingHom.id_apply, hsm, smul_eq_mul]
        exact e.map_mul c y
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  have : Module.Flat R S := Module.Flat.of_linearEquiv eL.symm
  have h0 : IsZero ((Koszul.seqComplexTensor f R).homology i) :=
    h.of_iso (Koszul.homologySelfIso f i)
  have h1 := KoszulC.homology_isZero_baseChange (S := S) f R i h0
  have h2 : IsZero ((Koszul.seqComplexTensor (R := S)
      (fun k => algebraMap R S (f k)) S).homology i) :=
    h1.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (Koszul.seqComplexTensorCongr (R := S) (fun k => algebraMap R S (f k))
        (Algebra.TensorProduct.rid R S S).toLinearEquiv).symm)
  have h3 : IsZero ((Koszul.seqComplex (R := S)
      (fun k => algebraMap R S (f k))).homology i) :=
    h2.of_iso (Koszul.homologySelfIso (R := S) (fun k => algebraMap R S (f k)) i).symm
  have hae : (fun k => algebraMap R S (f k)) = fun k => e (f k) := by
    funext k
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  exact hae ▸ h3

/-- Koszul exactness of a sequence in a fixed degree is invariant under a ring isomorphism,
stated for any sequence equal to the transported one. -/
private theorem koszulHomology_isZero_ringEquiv_iff {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) {r : ℕ} (f : Fin r → R) (g : Fin r → S) (hg : (fun k => e (f k)) = g)
    (i : ℕ) :
    IsZero ((Koszul.seqComplex f).homology i) ↔
      IsZero ((Koszul.seqComplex g).homology i) := by
  subst hg
  refine ⟨koszulHomology_isZero_of_ringEquiv e f i, fun h => ?_⟩
  have h' := koszulHomology_isZero_of_ringEquiv e.symm (fun k => e (f k)) i h
  have hff : (fun k => e.symm (e (f k))) = f := by funext k; exact e.symm_apply_apply (f k)
  exact hff ▸ h'

end KoszulRingEquiv

/-! ### The ideal generated by a sequence, under a ring isomorphism -/

section JidRingEquiv

/-- Membership in the ideal generated by a finite sequence is invariant under a ring
isomorphism. -/
private theorem mem_Jid_ringEquiv_iff {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {r : ℕ} (g : Fin r → R) (a : R) :
    a ∈ Jid g ↔ e a ∈ Jid (fun i => e (g i)) := by
  have hJ : Jid (fun i => e (g i)) = Ideal.map (e : R →+* S) (Jid g) :=
    Jid_map (e : R →+* S) g
  rw [hJ]
  refine ⟨fun h => Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  obtain ⟨b, hb, hba⟩ :=
    (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).mp h
  have : b = a := e.injective hba
  exact this ▸ hb

end JidRingEquiv


/-! ### Restriction of an ideal subsheaf to an open -/

section Restrict

variable {X : RingedSpace.{u}} (V : Opens X)

/-- An open of the restriction `X|_V`, read as an open of `X`. -/
def imOpen (W : Opens (X.restrict V.isOpenEmbedding)) : Opens X :=
  V.isOpenEmbedding.functor.obj W

/-- A point of `X|_V` lies in an open `W` of `X|_V` exactly when its image in `X` lies in
`imOpen V W`. -/
@[simp]
theorem mem_imOpen {W : Opens (X.restrict V.isOpenEmbedding)}
    {z : X.restrict V.isOpenEmbedding} : z.1 ∈ imOpen V W ↔ z ∈ W := by
  refine ⟨fun hz => ?_, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨y, hy, hyz⟩ := hz
  exact (Subtype.ext hyz : y = z) ▸ hy

/-- The image in `X` of an open of `X|_V` is contained in `V`. -/
theorem imOpen_le {W : Opens (X.restrict V.isOpenEmbedding)} : imOpen V W ≤ V := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

/-- `imOpen V` is monotone. -/
theorem imOpen_le_imOpen {W W' : Opens (X.restrict V.isOpenEmbedding)} (h : W ≤ W') :
    imOpen V W ≤ imOpen V W' := Set.image_mono h

/-- `imOpen V` reflects inclusions of opens of `X|_V`. -/
theorem le_of_imOpen_le_imOpen {W W' : Opens (X.restrict V.isOpenEmbedding)}
    (h : imOpen V W ≤ imOpen V W') : W ≤ W' := fun _ hz =>
  (mem_imOpen V).mp (h ((mem_imOpen V).mpr hz))

/-- Every open of `X` contained in `V` is the image of an open of `X|_V`. -/
theorem exists_imOpen_eq (U : Opens X) (hU : U ≤ V) :
    ∃ W : Opens (X.restrict V.isOpenEmbedding), imOpen V W = U := by
  refine ⟨⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩, ?_⟩
  ext z
  exact ⟨fun ⟨_, hy, hyz⟩ => hyz ▸ hy, fun hz => ⟨⟨z, hU hz⟩, hz, rfl⟩⟩

/-- **An ideal subsheaf, restricted to an open.** Over an open of `X|_V` it has the sections of
the original ideal subsheaf over the corresponding open of `X`. -/
noncomputable def restrictSubmodule (J : (structureSheafModule X).Submodule) :
    (structureSheafModule (X.restrict V.isOpenEmbedding)).Submodule where
  toSubmodule :=
    { obj W := J.obj (op (imOpen V W.unop))
      map {W W'} g := fun s hs => J.toSubmodule.map (V.isOpenEmbedding.functor.map g.unop).op hs }
  isSheaf := by
    intro W s hs
    refine J.isSheaf (X := op (imOpen V W.unop)) s ((Opens.mem_grothendieckTopology _).mpr ?_)
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨W₀, g, hgs, hyW₀⟩ := (Opens.mem_grothendieckTopology _).mp hs y hy
    exact ⟨imOpen V W₀, V.isOpenEmbedding.functor.map g, hgs, ⟨y, hyW₀, rfl⟩⟩

/-- The sections of `restrictSubmodule V J` over an open `W` of `X|_V` are the sections of `J`
over `imOpen V W`. -/
theorem restrictSubmodule_obj (J : (structureSheafModule X).Submodule)
    (W : Opens (X.restrict V.isOpenEmbedding)) :
    (restrictSubmodule V J).obj (op W) = J.obj (op (imOpen V W)) := rfl

/-- The germ of a section of `X|_V` is, under the identification of the stalks, the germ of that
section on `X`. -/
theorem restrictStalkEquiv_germ (W : Opens (X.restrict V.isOpenEmbedding))
    (z : X.restrict V.isOpenEmbedding) (hz : z ∈ W)
    (s : (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) :
    restrictStalkEquiv X V z.1 z.2
        ((X.restrict V.isOpenEmbedding).presheaf.germ W z hz s)
      = X.presheaf.germ (imOpen V W) z.1 ⟨z, hz, rfl⟩ s :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    X.toPresheafedSpace V.isOpenEmbedding W z hz s

/-- The germs of a family of sections of `X|_V` are, under the identification of the stalks, its
germs on `X`. -/
theorem restrictStalkEquiv_germFamily {r : ℕ} (W : Opens (X.restrict V.isOpenEmbedding))
    (f : Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W))
    (z : X.restrict V.isOpenEmbedding) (hz : z ∈ W) :
    (fun i => restrictStalkEquiv X V z.1 z.2
        (germFamily (X.restrict V.isOpenEmbedding) W f z hz i))
      = germFamily X (imOpen V W) f z.1 ⟨z, hz, rfl⟩ := by
  funext i
  exact restrictStalkEquiv_germ V W z hz (f i)

end Restrict

/-! ### Transport of the three local conditions across a restriction -/

section Transport

variable {X : RingedSpace.{u}} (V : Opens X)

/-- **The support of the quotient is local.** A point of `V` lies in the support of the quotient
by the restricted ideal subsheaf exactly when it lies in the support of the quotient by the
original one. -/
theorem mem_idealQuotientSupport_restrictSubmodule_iff
    (J : (structureSheafModule X).Submodule) (z : X.restrict V.isOpenEmbedding) :
    z ∈ idealQuotientSupport (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      z.1 ∈ idealQuotientSupport X J := by
  rw [← not_iff_not, notMem_idealQuotientSupport_iff, notMem_idealQuotientSupport_iff]
  constructor
  · rintro ⟨W, hzW, h1⟩
    exact ⟨imOpen V W, ⟨z, hzW, rfl⟩, h1⟩
  · rintro ⟨U, hzU, h1⟩
    obtain ⟨W, hW⟩ := exists_imOpen_eq V (U ⊓ V) inf_le_right
    have hzW : z ∈ W := (mem_imOpen V).mp (hW ▸ ⟨hzU, z.2⟩)
    refine ⟨W, hzW, ?_⟩
    have h := J.toSubmodule.map_mem
      (homOfLE (show imOpen V W ≤ U from hW ▸ inf_le_left)).op h1
    have hmo : (ConcreteCategory.hom ((structureSheafModule X).val.map
        (homOfLE (show imOpen V W ≤ U from hW ▸ inf_le_left)).op))
          (1 : X.presheaf.obj (op U)) = (1 : X.presheaf.obj (op (imOpen V W))) :=
      map_one (X.presheaf.map
        (homOfLE (show imOpen V W ≤ U from hW ▸ inf_le_left)).op).hom
    exact hmo ▸ h

/-- **Generation of an ideal subsheaf by sections is local.** A family of sections over an open
of `X|_V` generates the restricted ideal subsheaf exactly when it generates the original one
over the corresponding open of `X`. -/
theorem isGeneratedByOn_restrictSubmodule_iff (J : (structureSheafModule X).Submodule)
    {r : ℕ} (W : Opens (X.restrict V.isOpenEmbedding))
    (f : Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) :
    IsGeneratedByOn (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) W f ↔
      IsGeneratedByOn X J (imOpen V W) f := by
  have key : ∀ (W' : Opens (X.restrict V.isOpenEmbedding)) (hW' : W' ≤ W)
      (s : (X.restrict V.isOpenEmbedding).presheaf.obj (op W')),
      ((∀ (z : X.restrict V.isOpenEmbedding) (hz : z ∈ W'),
          (X.restrict V.isOpenEmbedding).presheaf.germ W' z hz s ∈
            Jid (germFamily (X.restrict V.isOpenEmbedding) W f z (hW' hz))) ↔
        ∀ (y : X) (hy : y ∈ imOpen V W'),
          X.presheaf.germ (imOpen V W') y hy s ∈
            Jid (germFamily X (imOpen V W) f y (imOpen_le_imOpen V hW' hy))) := by
    intro W' hW' s
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have h1 := (mem_Jid_ringEquiv_iff (restrictStalkEquiv X V z.1 z.2)
        (germFamily (X.restrict V.isOpenEmbedding) W f z (hW' hz)) _).mp (h z hz)
      rw [restrictStalkEquiv_germFamily V W f z (hW' hz),
        restrictStalkEquiv_germ V W' z hz s] at h1
      exact h1
    · intro h z hz
      have h1 := h z.1 ⟨z, hz, rfl⟩
      rw [← restrictStalkEquiv_germFamily V W f z (hW' hz),
        ← restrictStalkEquiv_germ V W' z hz s] at h1
      exact (mem_Jid_ringEquiv_iff (restrictStalkEquiv X V z.1 z.2)
        (germFamily (X.restrict V.isOpenEmbedding) W f z (hW' hz)) _).mpr h1
  constructor
  · intro h U hU
    obtain ⟨W', hW'⟩ := exists_imOpen_eq V U (hU.trans (imOpen_le V))
    subst hW'
    have hle : W' ≤ W := le_of_imOpen_le_imOpen V hU
    refine Submodule.ext fun s => ?_
    exact (Iff.of_eq (congrArg (fun I => s ∈ I) (h W' hle))).trans
      ((mem_generatedIdealOn_iff W f W' hle s).trans
        ((key W' hle s).trans
          (mem_generatedIdealOn_iff (imOpen V W) f (imOpen V W') hU s).symm))
  · intro h W' hW'
    refine Submodule.ext fun s => ?_
    exact (Iff.of_eq (congrArg (fun I => s ∈ I)
        (h (imOpen V W') (imOpen_le_imOpen V hW')))).trans
      ((mem_generatedIdealOn_iff (imOpen V W) f (imOpen V W')
          (imOpen_le_imOpen V hW') s).trans
        ((key W' hW' s).symm.trans (mem_generatedIdealOn_iff W f W' hW' s).symm))

/-- **Koszul exactness of a sequence of sections is local.** -/
theorem isKoszulSequenceExactOn_restrict_iff {r : ℕ}
    (W : Opens (X.restrict V.isOpenEmbedding))
    (f : Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) (P : ℕ → Prop) :
    IsKoszulSequenceExactOn (X.restrict V.isOpenEmbedding) W f P ↔
      IsKoszulSequenceExactOn X (imOpen V W) f P := by
  constructor
  · intro h y hy j hj
    obtain ⟨z, hz, rfl⟩ := hy
    exact (koszulHomology_isZero_ringEquiv_iff (restrictStalkEquiv X V z.1 z.2) _ _
      (restrictStalkEquiv_germFamily V W f z hz) j).mp (h z hz j hj)
  · intro h z hz j hj
    exact (koszulHomology_isZero_ringEquiv_iff (restrictStalkEquiv X V z.1 z.2) _ _
      (restrictStalkEquiv_germFamily V W f z hz) j).mpr (h z.1 ⟨z, hz, rfl⟩ j hj)

/-- **The elementary relation condition on the germs of a sequence of sections is local.** -/
theorem forall_isQuasiRegularRel_germFamily_restrict_iff {r : ℕ}
    (W : Opens (X.restrict V.isOpenEmbedding))
    (f : Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) :
    (∀ (z : X.restrict V.isOpenEmbedding) (hz : z ∈ W),
        IsQuasiRegularRel (germFamily (X.restrict V.isOpenEmbedding) W f z hz)) ↔
      ∀ (y : X) (hy : y ∈ imOpen V W), IsQuasiRegularRel (germFamily X (imOpen V W) f y hy) := by
  constructor
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact isQuasiRegularRel_congr (restrictStalkEquiv_germFamily V W f z hz)
      (isQuasiRegularRel_ringEquiv (restrictStalkEquiv X V z.1 z.2) _ (h z hz))
  · intro h z hz
    have h1 := h z.1 ⟨z, hz, rfl⟩
    rw [← restrictStalkEquiv_germFamily V W f z hz] at h1
    refine isQuasiRegularRel_congr ?_
      (isQuasiRegularRel_ringEquiv (restrictStalkEquiv X V z.1 z.2).symm _ h1)
    funext i
    exact (restrictStalkEquiv X V z.1 z.2).symm_apply_apply _

end Transport


/-! ### Shrinking a local witness -/

section Shrink

/-- Vanishing of Koszul homology only depends on the sequence. -/
private theorem koszulHomology_isZero_congr {R : Type u} [CommRing R] {r : ℕ}
    {f g : Fin r → R} (h : f = g) (j : ℕ)
    (hz : IsZero ((Koszul.seqComplex f).homology j)) :
    IsZero ((Koszul.seqComplex g).homology j) := by
  subst h
  exact hz

variable {X : RingedSpace.{u}} {U : Opens X} {r : ℕ} {f : Fin r → X.presheaf.obj (op U)}

/-- Koszul exactness of a sequence of sections is inherited by any smaller open. -/
theorem IsKoszulSequenceExactOn.of_le {P : ℕ → Prop} (h : IsKoszulSequenceExactOn X U f P)
    (U' : Opens X) (hU' : U' ≤ U) :
    IsKoszulSequenceExactOn X U' (fun i => X.presheaf.map (homOfLE hU').op (f i)) P := by
  intro y hy j hj
  exact koszulHomology_isZero_congr (germFamily_res U U' hU' f y hy).symm j
    (h y (hU' hy) j hj)

/-- The sheaf quasi-regularity condition on a sequence of sections is inherited by any smaller
open. -/
theorem isQuasiRegularMap_isIso_of_le
    (h : IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun i => sectionOnRestriction X U (f i))).hom)
    (U' : Opens X) (hU' : U' ≤ U) :
    IsIso (quasiRegularMap (X.restrict U'.isOpenEmbedding)
      (fun i => sectionOnRestriction X U' (X.presheaf.map (homOfLE hU').op (f i)))).hom := by
  refine (isQuasiRegularMapIso_iff_forall_germ X U'
    (fun i => X.presheaf.map (homOfLE hU').op (f i))).mpr fun y hy => ?_
  rw [germFamily_res U U' hU' f y hy]
  exact (isQuasiRegularMapIso_iff_forall_germ X U f).mp h y (hU' hy)

end Shrink

/-! ### The three local conditions on a restricted ideal sheaf -/

section Master

variable {X : RingedSpace.{u}} (V : Opens X) (J : (structureSheafModule X).Submodule)

/-- Every point of `V` in the support of `O_X / J` has, on a neighbourhood contained in `V`, a
generating sequence of `J` satisfying `Q`. -/
private def HasWitnessIn (Q : ∀ (U : Opens X) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop) :
    Prop :=
  ∀ y : X, y ∈ V → y ∈ idealQuotientSupport X J →
    ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ V) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
      Q U r f ∧ IsGeneratedByOn X J U f

/-- A witness condition `Q'` on `X|_V` that is read as `Q` on `X` makes the condition on the
restricted ideal subsheaf a condition on the ambient space. -/
private theorem forall_exists_restrict_iff
    (Q : ∀ (U : Opens X) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop)
    (Q' : ∀ (W : Opens (X.restrict V.isOpenEmbedding)) (r : ℕ),
      (Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) → Prop)
    (hQ : ∀ W r f, Q' W r f ↔ Q (imOpen V W) r f) :
    (∀ z : X.restrict V.isOpenEmbedding,
        z ∈ idealQuotientSupport (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) →
        ∃ (W : Opens (X.restrict V.isOpenEmbedding)) (_ : z ∈ W) (r : ℕ)
          (f : Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)),
          Q' W r f ∧ IsGeneratedByOn (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) W f) ↔
      HasWitnessIn V J Q := by
  constructor
  · intro h y hyV hySupp
    obtain ⟨W, hzW, r, f, hK, hG⟩ := h ⟨y, hyV⟩
      ((mem_idealQuotientSupport_restrictSubmodule_iff V J ⟨y, hyV⟩).mpr hySupp)
    exact ⟨imOpen V W, ⟨⟨y, hyV⟩, hzW, rfl⟩, imOpen_le V, r, f, (hQ W r f).mp hK,
      (isGeneratedByOn_restrictSubmodule_iff V J W f).mp hG⟩
  · intro h z hz
    obtain ⟨U, hyU, hUV, r, f, hK, hG⟩ := h z.1 z.2
      ((mem_idealQuotientSupport_restrictSubmodule_iff V J z).mp hz)
    obtain ⟨W, hW⟩ := exists_imOpen_eq V U hUV
    subst hW
    exact ⟨W, (mem_imOpen V).mp hyU, r, f, (hQ W r f).mpr hK,
      (isGeneratedByOn_restrictSubmodule_iff V J W f).mpr hG⟩

/-- **Koszul-regularity of a restricted ideal subsheaf, read on the ambient space.** The
condition of Stacks tag 063D part (2) for `J|_V` on `X|_V` says exactly that every point of `V`
in the support of `O_X / J` has a Koszul-regular generating sequence for `J` on a neighbourhood
*contained in `V`*. -/
theorem isKoszulRegularIdealSheaf_restrictSubmodule_iff :
    IsKoszulRegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      ∀ y : X, y ∈ V → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ V) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
          IsKoszulSequenceExactOn X U f (fun j => 0 < j) ∧ IsGeneratedByOn X J U f :=
  forall_exists_restrict_iff V J _ _ fun W _ f => isKoszulSequenceExactOn_restrict_iff V W f _

/-- **`H₁`-regularity of a restricted ideal subsheaf, read on the ambient space.** -/
theorem isH1RegularIdealSheaf_restrictSubmodule_iff :
    IsH1RegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      ∀ y : X, y ∈ V → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ V) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
          IsKoszulSequenceExactOn X U f (fun j => j = 1) ∧ IsGeneratedByOn X J U f :=
  forall_exists_restrict_iff V J _ _ fun W _ f => isKoszulSequenceExactOn_restrict_iff V W f _

/-- **Quasi-regularity of a restricted ideal subsheaf, read on the ambient space.** -/
theorem isQuasiRegularIdealSheaf_restrictSubmodule_iff :
    IsQuasiRegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      ∀ y : X, y ∈ V → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ V) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
          IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
              (fun i => sectionOnRestriction X U (f i))).hom ∧ IsGeneratedByOn X J U f :=
  forall_exists_restrict_iff V J _ _ fun W _ f =>
    (isQuasiRegularMapIso_iff_forall_germ (X.restrict V.isOpenEmbedding) W f).trans
      ((forall_isQuasiRegularRel_germFamily_restrict_iff V W f).trans
        (isQuasiRegularMapIso_iff_forall_germ X (imOpen V W) f).symm)

/-- A witness condition `Q` that survives shrinking the open passes from `A` to any `B` that
agrees with `A` on the support. -/
private theorem hasWitnessIn_mono {A B : Opens X}
    {Q : ∀ (U : Opens X) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop}
    (hQ : ∀ {U : Opens X} {r : ℕ} {f : Fin r → X.presheaf.obj (op U)} (U' : Opens X)
      (hU' : U' ≤ U), Q U r f → Q U' r (fun i => X.presheaf.map (homOfLE hU').op (f i)))
    (hAB : ∀ y : X, y ∈ idealQuotientSupport X J → y ∈ B → y ∈ A)
    (h : HasWitnessIn A J Q) : HasWitnessIn B J Q := by
  intro y hyB hySupp
  obtain ⟨U, hyU, _, r, f, hQf, hG⟩ := h y (hAB y hySupp hyB) hySupp
  exact ⟨U ⊓ B, ⟨hyU, hyB⟩, inf_le_right, r,
    fun i => X.presheaf.map (homOfLE (inf_le_left (a := U) (b := B))).op (f i),
    hQ _ inf_le_left hQf, isGeneratedByOn_of_le U f hG _ inf_le_left⟩

end Master


/-! ### Nested restrictions -/

section Nested

variable {X : RingedSpace.{u}} (V : Opens X) (A : Opens (X.restrict V.isOpenEmbedding))
  (J : (structureSheafModule X).Submodule)

/-- The witness condition on `(X|_V)|_A` is the one on `X|_{imOpen V A}`, read on the ambient
space. -/
private theorem hasWitnessIn_restrict_restrict_iff
    (Q : ∀ (U : Opens X) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop)
    (Q' : ∀ (W : Opens (X.restrict V.isOpenEmbedding)) (r : ℕ),
      (Fin r → (X.restrict V.isOpenEmbedding).presheaf.obj (op W)) → Prop)
    (hQ : ∀ W r f, Q' W r f ↔ Q (imOpen V W) r f) :
    HasWitnessIn A (restrictSubmodule V J) Q' ↔ HasWitnessIn (imOpen V A) J Q := by
  constructor
  · intro h y hyA hySupp
    obtain ⟨z, hzA, rfl⟩ := hyA
    obtain ⟨U, hzU, hUA, r, f, hK, hG⟩ := h z hzA
      ((mem_idealQuotientSupport_restrictSubmodule_iff V J z).mpr hySupp)
    exact ⟨imOpen V U, ⟨z, hzU, rfl⟩, imOpen_le_imOpen V hUA, r, f, (hQ U r f).mp hK,
      (isGeneratedByOn_restrictSubmodule_iff V J U f).mp hG⟩
  · intro h z hzA hzSupp
    obtain ⟨U, hyU, hUA, r, f, hK, hG⟩ := h z.1 ⟨z, hzA, rfl⟩
      ((mem_idealQuotientSupport_restrictSubmodule_iff V J z).mp hzSupp)
    obtain ⟨U', hU'⟩ := exists_imOpen_eq V U (hUA.trans (imOpen_le V))
    subst hU'
    exact ⟨U', (mem_imOpen V).mp hyU, le_of_imOpen_le_imOpen V hUA, r, f, (hQ U' r f).mpr hK,
      (isGeneratedByOn_restrictSubmodule_iff V J U' f).mpr hG⟩

/-- **Koszul-regularity of a twice-restricted ideal subsheaf, read on the ambient space.** The
space `(X|_V)|_A` is not the restriction of `X` to any open — it is only *isomorphic* to
`X|_{imOpen V A}` — but the condition of Stacks tag 063D part (2) on it is again a condition on
the ambient `X`, and it is the same one. -/
theorem isKoszulRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff :
    IsKoszulRegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      ∀ y : X, y ∈ imOpen V A → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ imOpen V A) (r : ℕ)
          (f : Fin r → X.presheaf.obj (op U)),
          IsKoszulSequenceExactOn X U f (fun j => 0 < j) ∧ IsGeneratedByOn X J U f :=
  (isKoszulRegularIdealSheaf_restrictSubmodule_iff A (restrictSubmodule V J)).trans
    (hasWitnessIn_restrict_restrict_iff V A J _ _ fun U _ f =>
      isKoszulSequenceExactOn_restrict_iff V U f _)

/-- **`H₁`-regularity of a twice-restricted ideal subsheaf, read on the ambient space.** -/
theorem isH1RegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff :
    IsH1RegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      ∀ y : X, y ∈ imOpen V A → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ imOpen V A) (r : ℕ)
          (f : Fin r → X.presheaf.obj (op U)),
          IsKoszulSequenceExactOn X U f (fun j => j = 1) ∧ IsGeneratedByOn X J U f :=
  (isH1RegularIdealSheaf_restrictSubmodule_iff A (restrictSubmodule V J)).trans
    (hasWitnessIn_restrict_restrict_iff V A J _ _ fun U _ f =>
      isKoszulSequenceExactOn_restrict_iff V U f _)

/-- **Quasi-regularity of a twice-restricted ideal subsheaf, read on the ambient space.** -/
theorem isQuasiRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff :
    IsQuasiRegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      ∀ y : X, y ∈ imOpen V A → y ∈ idealQuotientSupport X J →
        ∃ (U : Opens X) (_ : y ∈ U) (_ : U ≤ imOpen V A) (r : ℕ)
          (f : Fin r → X.presheaf.obj (op U)),
          IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
              (fun i => sectionOnRestriction X U (f i))).hom ∧ IsGeneratedByOn X J U f :=
  (isQuasiRegularIdealSheaf_restrictSubmodule_iff A (restrictSubmodule V J)).trans
    (hasWitnessIn_restrict_restrict_iff V A J _ _ fun U _ f =>
      (isQuasiRegularMapIso_iff_forall_germ (X.restrict V.isOpenEmbedding) U f).trans
        ((forall_isQuasiRegularRel_germFamily_restrict_iff V U f).trans
          (isQuasiRegularMapIso_iff_forall_germ X (imOpen V U) f).symm))

/-- **Transport of Koszul-regularity across the nesting isomorphism.** The twice-restricted
ideal subsheaf on `(X|_V)|_A` satisfies the condition of Stacks tag 063D part (2) exactly when
the once-restricted one on `X|_{imOpen V A}` does, even though the two spaces are only
isomorphic. -/
theorem isKoszulRegularIdealSheaf_restrictSubmodule_nested_iff :
    IsKoszulRegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      IsKoszulRegularIdealSheaf (X.restrict (imOpen V A).isOpenEmbedding)
        (restrictSubmodule (imOpen V A) J) :=
  (isKoszulRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V A J).trans
    (isKoszulRegularIdealSheaf_restrictSubmodule_iff (imOpen V A) J).symm

/-- **Transport of `H₁`-regularity across the nesting isomorphism.** -/
theorem isH1RegularIdealSheaf_restrictSubmodule_nested_iff :
    IsH1RegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      IsH1RegularIdealSheaf (X.restrict (imOpen V A).isOpenEmbedding)
        (restrictSubmodule (imOpen V A) J) :=
  (isH1RegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V A J).trans
    (isH1RegularIdealSheaf_restrictSubmodule_iff (imOpen V A) J).symm

/-- **Transport of quasi-regularity across the nesting isomorphism.** -/
theorem isQuasiRegularIdealSheaf_restrictSubmodule_nested_iff :
    IsQuasiRegularIdealSheaf ((X.restrict V.isOpenEmbedding).restrict A.isOpenEmbedding)
        (restrictSubmodule A (restrictSubmodule V J)) ↔
      IsQuasiRegularIdealSheaf (X.restrict (imOpen V A).isOpenEmbedding)
        (restrictSubmodule (imOpen V A) J) :=
  (isQuasiRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V A J).trans
    (isQuasiRegularIdealSheaf_restrictSubmodule_iff (imOpen V A) J).symm

end Nested


/-! ### Independence of the chosen open -/

section Independence

variable {X : RingedSpace.{u}} (J : (structureSheafModule X).Submodule)

/-- Two opens that agree on the support have the same witnesses, provided `Q` survives shrinking
the open. -/
private theorem hasWitnessIn_congr_iff {V V' : Opens X}
    {Q : ∀ (U : Opens X) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop}
    (h : ∀ y : X, y ∈ idealQuotientSupport X J → (y ∈ V ↔ y ∈ V'))
    (hQ : ∀ {U : Opens X} {r : ℕ} {f : Fin r → X.presheaf.obj (op U)} (U' : Opens X)
      (hU' : U' ≤ U), Q U r f → Q U' r (fun i => X.presheaf.map (homOfLE hU').op (f i))) :
    HasWitnessIn V J Q ↔ HasWitnessIn V' J Q :=
  ⟨hasWitnessIn_mono J hQ fun y hy => (h y hy).mpr,
    hasWitnessIn_mono J hQ fun y hy => (h y hy).mp⟩

/-- **Stacks tag 063J, part (2): independence of the chosen open.** Two opens of `X` that cut
out the same part of the support of `O_X / J` give the same Koszul-regularity condition on the
restricted ideal subsheaf.

This is what makes part (2) of Stacks tag 063J well posed: the condition of Stacks tag 063D is
checked near the points of the support, and the chosen open only enters by bounding the
neighbourhoods on which a generating sequence is produced. -/
theorem isKoszulRegularIdealSheaf_restrictSubmodule_congr (V V' : Opens X)
    (h : ∀ y : X, y ∈ idealQuotientSupport X J → (y ∈ V ↔ y ∈ V')) :
    IsKoszulRegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      IsKoszulRegularIdealSheaf (X.restrict V'.isOpenEmbedding) (restrictSubmodule V' J) :=
  (isKoszulRegularIdealSheaf_restrictSubmodule_iff V J).trans
    ((hasWitnessIn_congr_iff J h fun U' hU' hK => hK.of_le U' hU').trans
      (isKoszulRegularIdealSheaf_restrictSubmodule_iff V' J).symm)

/-- **Stacks tag 063J, part (3): independence of the chosen open.** Two opens of `X` that cut
out the same part of the support of `O_X / J` give the same `H₁`-regularity condition on the
restricted ideal subsheaf. -/
theorem isH1RegularIdealSheaf_restrictSubmodule_congr (V V' : Opens X)
    (h : ∀ y : X, y ∈ idealQuotientSupport X J → (y ∈ V ↔ y ∈ V')) :
    IsH1RegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      IsH1RegularIdealSheaf (X.restrict V'.isOpenEmbedding) (restrictSubmodule V' J) :=
  (isH1RegularIdealSheaf_restrictSubmodule_iff V J).trans
    ((hasWitnessIn_congr_iff J h fun U' hU' hK => hK.of_le U' hU').trans
      (isH1RegularIdealSheaf_restrictSubmodule_iff V' J).symm)

/-- **Stacks tag 063J, part (4): independence of the chosen open.** Two opens of `X` that cut
out the same part of the support of `O_X / J` give the same quasi-regularity condition on the
restricted ideal subsheaf. -/
theorem isQuasiRegularIdealSheaf_restrictSubmodule_congr (V V' : Opens X)
    (h : ∀ y : X, y ∈ idealQuotientSupport X J → (y ∈ V ↔ y ∈ V')) :
    IsQuasiRegularIdealSheaf (X.restrict V.isOpenEmbedding) (restrictSubmodule V J) ↔
      IsQuasiRegularIdealSheaf (X.restrict V'.isOpenEmbedding) (restrictSubmodule V' J) :=
  (isQuasiRegularIdealSheaf_restrictSubmodule_iff V J).trans
    (Iff.trans (hasWitnessIn_congr_iff J h fun U' hU' hQ => isQuasiRegularMap_isIso_of_le hQ U' hU')
      (isQuasiRegularIdealSheaf_restrictSubmodule_iff V' J).symm)

end Independence


/-! ### Two admissible opens for an immersion -/

section Immersion

variable {Z X : Scheme.{u}}

/-- **Away from the closure of the image, the defining ideal sheaf is the whole structure
sheaf.** On an open missing the closure of the image the morphism has empty source, so every
section of `O_X` dies in the pushforward; in particular the unit section does. -/
theorem notMem_idealQuotientSupport_definingIdealOfHom_of_notMem_closure (i : Z ⟶ X) (y : X)
    (hy : y ∉ closure (Set.range i.base)) :
    y ∉ idealQuotientSupport X.toLocallyRingedSpace.toRingedSpace (definingIdealOfHom i) := by
  set W : X.Opens := ⟨(closure (Set.range i.base))ᶜ, isClosed_closure.isOpen_compl⟩ with hWdef
  have hpre : i ⁻¹ᵁ W = ⊥ := by
    ext z
    refine ⟨fun hz => ?_, fun hz => hz.elim⟩
    exact absurd (subset_closure (Set.mem_range_self z)) hz
  have hsub : Subsingleton Γ(Z, i ⁻¹ᵁ W) := by rw [hpre]; infer_instance
  refine notMem_idealQuotientSupport_of_one_mem (definingIdealOfHom i) y W hy ?_
  show (i.app W).hom (1 : Γ(X, W)) = 0
  exact Subsingleton.elim _ _

/-- The image of a morphism that factors as a morphism into an open subscheme lies in that
open. -/
theorem range_base_subset_of_comp_ι_eq (i : Z ⟶ X) (V : X.Opens) (j : Z ⟶ V.toScheme)
    (hij : j ≫ V.ι = i) : Set.range i.base ⊆ (V : Set X) := by
  rw [← hij]
  rintro x ⟨z, rfl⟩
  exact (j.base z).2

/-- **Two admissible opens for an immersion cut out the same part of the support.** If `i` is
closed in both `V` and `V'`, then a point of the support of the quotient by the defining ideal
sheaf of `i` on the ambient `X` lies in `V` exactly when it lies in `V'`: it lies in the closure
of the image, hence — being in an open in which `i` is closed, so in `i.coborderRange` — in the
image itself, which is contained in both.

This is the hypothesis that the independence statements of this file consume. -/
theorem mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom (i : Z ⟶ X) [IsImmersion i]
    (V V' : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i)
    (j' : Z ⟶ V'.toScheme) [IsClosedImmersion j'] (hij' : j' ≫ V'.ι = i) (y : X)
    (hy : y ∈ idealQuotientSupport X.toLocallyRingedSpace.toRingedSpace
      (definingIdealOfHom i)) :
    y ∈ V ↔ y ∈ V' := by
  have hclos : y ∈ closure (Set.range i.base) := by
    by_contra hc
    exact notMem_idealQuotientSupport_definingIdealOfHom_of_notMem_closure i y hc hy
  have key : ∀ (A : X.Opens) (a : Z ⟶ A.toScheme), IsClosedImmersion a → a ≫ A.ι = i →
      y ∈ A → y ∈ Set.range i.base := by
    intro A a ha hA hyA
    have _ := ha
    have hAC : A ≤ i.coborderRange := le_coborderRange_of_isClosedImmersion i A a hA
    have hmem : y ∈ coborder (Set.range i.base) := hAC hyA
    exact (mem_coborder_iff_imp.mp hmem) hclos
  exact ⟨fun hyV => range_base_subset_of_comp_ι_eq i V' j' hij' (key V j ‹_› hij hyV),
    fun hyV' => range_base_subset_of_comp_ι_eq i V j hij (key V' j' ‹_› hij' hyV')⟩

/-- **Stacks tag 063J, part (2): independence of the chosen open.** For an immersion `i : Z ⟶ X`
and two opens of `X` in which `i` is closed, the Koszul-regularity condition of Stacks tag 063D
on the restriction of the defining ideal sheaf of `i` is the same on both. -/
@[stacks 063J "part (2): independence of the chosen open, for the restricted defining ideal"]
theorem isKoszulRegularIdealSheaf_definingIdealOfHom_congr (i : Z ⟶ X) [IsImmersion i]
    (V V' : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i)
    (j' : Z ⟶ V'.toScheme) [IsClosedImmersion j'] (hij' : j' ≫ V'.ι = i) :
    IsKoszulRegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V (definingIdealOfHom i)) ↔
      IsKoszulRegularIdealSheaf V'.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V' (definingIdealOfHom i)) :=
  isKoszulRegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i) V V'
    (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i V V' j hij j' hij')

/-- **Stacks tag 063J, part (3): independence of the chosen open.** -/
@[stacks 063J "part (3): independence of the chosen open, for the restricted defining ideal"]
theorem isH1RegularIdealSheaf_definingIdealOfHom_congr (i : Z ⟶ X) [IsImmersion i]
    (V V' : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i)
    (j' : Z ⟶ V'.toScheme) [IsClosedImmersion j'] (hij' : j' ≫ V'.ι = i) :
    IsH1RegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V (definingIdealOfHom i)) ↔
      IsH1RegularIdealSheaf V'.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V' (definingIdealOfHom i)) :=
  isH1RegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i) V V'
    (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i V V' j hij j' hij')

/-- **Stacks tag 063J, part (4): independence of the chosen open.** -/
@[stacks 063J "part (4): independence of the chosen open, for the restricted defining ideal"]
theorem isQuasiRegularIdealSheaf_definingIdealOfHom_congr (i : Z ⟶ X) [IsImmersion i]
    (V V' : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i)
    (j' : Z ⟶ V'.toScheme) [IsClosedImmersion j'] (hij' : j' ≫ V'.ι = i) :
    IsQuasiRegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V (definingIdealOfHom i)) ↔
      IsQuasiRegularIdealSheaf V'.toScheme.toLocallyRingedSpace.toRingedSpace
        (restrictSubmodule V' (definingIdealOfHom i)) :=
  isQuasiRegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i) V V'
    (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i V V' j hij j' hij')

/-! ### The restricted ambient ideal sheaf is the defining ideal sheaf of the factor -/

/-- **The restriction of the ambient defining ideal sheaf is the defining ideal sheaf of the
factor.** If `i : Z ⟶ X` factors as `j : Z ⟶ V` through an open `V ⊆ X`, then the restriction to
`V` of the defining ideal sheaf of `i` on the ambient `X` is the defining ideal sheaf of `j`.

Both sides have, over an open `W` of `V`, the sections of `O_X` over `V.ι ''ᵁ W` killed by the
map on sections induced by `i`, resp. by `j`.  Identifying the two compares `i.app (V.ι ''ᵁ W)`
with `j.app W`, whose targets are the sections of `O_Z` over `i ⁻¹ᵁ (V.ι ''ᵁ W)` and over
`j ⁻¹ᵁ W`; those are equal opens of `Z` but not syntactically identical, since
`V.ι ⁻¹ᵁ (V.ι ''ᵁ W) = W` is `Scheme.Hom.preimage_image_eq` and not `rfl`.  The comparison
therefore goes through a transport along that equality of opens, which is where one of the two
`eqToHom`s of this file sits (the other is in `restrictSubmodule_definingIdealOfHom_resLE`, for
the same reason).  Restriction along an equality of opens is an isomorphism, hence injective, so
it does not change the kernel. -/
theorem restrictSubmodule_definingIdealOfHom (i : Z ⟶ X) (V : X.Opens) (j : Z ⟶ V.toScheme)
    (hij : j ≫ V.ι = i) :
    restrictSubmodule V (definingIdealOfHom i) = definingIdealOfHom j := by
  subst hij
  refine eq_definingIdealOfHom_of_mem_iff j _ fun W s => ?_
  have e : V.ι ⁻¹ᵁ (V.ι ''ᵁ W) = W := V.ι.preimage_image_eq W
  have e2 : (j ≫ V.ι) ⁻¹ᵁ (V.ι ''ᵁ W) = j ⁻¹ᵁ W := by rw [Scheme.Hom.comp_preimage, e]
  have hAB : V.ι.app (V.ι ''ᵁ W) ≫ V.toScheme.presheaf.map (eqToHom e.symm).op = 𝟙 _ :=
    ((X.presheaf.map_comp _ _).symm.trans
      (congrArg X.presheaf.map (Subsingleton.elim _ (𝟙 _)))).trans (X.presheaf.map_id _)
  have key : (j ≫ V.ι).app (V.ι ''ᵁ W) = j.app W ≫ Z.presheaf.map (eqToHom e2).op := by
    rw [Scheme.Hom.comp_app, Scheme.Hom.app_eq j e, ← Category.assoc, hAB]
    exact Category.id_comp _
  have hinj : Function.Injective (ConcreteCategory.hom (Z.presheaf.map (eqToHom e2).op)) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  show ((j ≫ V.ι).app (V.ι ''ᵁ W)).hom s = 0 ↔ (j.app W).hom s = 0
  have val : ((j ≫ V.ι).app (V.ι ''ᵁ W)).hom s
      = (Z.presheaf.map (eqToHom e2).op).hom ((j.app W).hom s) := by rw [key]; rfl
  exact (iff_of_eq (congrArg (· = 0) val)).trans (map_eq_zero_iff _ hinj)

/-- The restriction to the canonical open `i.coborderRange` of the defining ideal sheaf of an
immersion `i` on the ambient `X` is the defining ideal sheaf of its canonical closed factor
`i.liftCoborder`, i.e. `definingIdeal i`. -/
theorem restrictSubmodule_coborderRange_definingIdealOfHom (i : Z ⟶ X) [IsImmersion i] :
    restrictSubmodule i.coborderRange (definingIdealOfHom i) = definingIdealOfHom i.liftCoborder :=
  restrictSubmodule_definingIdealOfHom i i.coborderRange i.liftCoborder i.liftCoborder_ι

/-- **Stacks tag 063J, part (2): independence of the chosen open.** An immersion is
Koszul-regular exactly when the defining ideal sheaf of its closed factor through *any* open in
which it is closed is a Koszul-regular ideal sheaf — not only the canonical one. -/
@[stacks 063J "part (2): independence of the chosen open"]
theorem isKoszulRegularImmersion_iff_of_open (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i) :
    IsKoszulRegularImmersion i ↔
      IsKoszulRegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom j) := by
  refine (isKoszulRegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).trans ?_
  rw [← restrictSubmodule_definingIdealOfHom i V j hij]
  exact isKoszulRegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i)
    i.coborderRange V (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i
      i.coborderRange V i.liftCoborder i.liftCoborder_ι j hij)

/-- **Stacks tag 063J, part (3): independence of the chosen open.** -/
@[stacks 063J "part (3): independence of the chosen open"]
theorem isH1RegularImmersion_iff_of_open (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i) :
    IsH1RegularImmersion i ↔
      IsH1RegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom j) := by
  refine (isH1RegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).trans ?_
  rw [← restrictSubmodule_definingIdealOfHom i V j hij]
  exact isH1RegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i)
    i.coborderRange V (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i
      i.coborderRange V i.liftCoborder i.liftCoborder_ι j hij)

/-- **Stacks tag 063J, part (4): independence of the chosen open.** -/
@[stacks 063J "part (4): independence of the chosen open"]
theorem isQuasiRegularImmersion_iff_of_open (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (j : Z ⟶ V.toScheme) [IsClosedImmersion j] (hij : j ≫ V.ι = i) :
    IsQuasiRegularImmersion i ↔
      IsQuasiRegularIdealSheaf V.toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom j) := by
  refine (isQuasiRegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).trans ?_
  rw [← restrictSubmodule_definingIdealOfHom i V j hij]
  exact isQuasiRegularIdealSheaf_restrictSubmodule_congr (definingIdealOfHom i)
    i.coborderRange V (mem_iff_mem_of_mem_idealQuotientSupport_definingIdealOfHom i
      i.coborderRange V i.liftCoborder i.liftCoborder_ι j hij)

/-! ### Restricting the target of an immersion to an open -/

/-- The source open cut out on `i ⁻¹ᵁ V` by an open `W` of `V` is, read back inside `Z`, the
preimage under `i` of `W` read inside `X`. This is what makes the restriction of `i` to `V`
have the same sections-level kernel as `i` itself. -/
theorem image_preimage_resLE (i : Z ⟶ X) (V : X.Opens) (W : V.toScheme.Opens) :
    (i ⁻¹ᵁ V).ι ''ᵁ ((i.resLE V (i ⁻¹ᵁ V) le_rfl) ⁻¹ᵁ W) = i ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.resLE_preimage i le_rfl W,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr ((Opens.map i.base).map (V.ι_image_le W).hom).le

/-- **The restriction to `V` of the defining ideal sheaf of `i` is the defining ideal sheaf of
the restriction of `i` to `V`.** Over an open `W` of `V` both sides are the sections of `O_X`
over `V.ι ''ᵁ W` killed by `i`, resp. by `i.resLE V (i ⁻¹ᵁ V) le_rfl`; the two maps differ by
restriction along `image_preimage_resLE`, an equality of opens of `Z`, hence by an isomorphism,
which does not change the kernel.

This is the companion of `restrictSubmodule_definingIdealOfHom`: that lemma restricts the
*target* of a factorization with the source fixed, this one restricts source and target
together. -/
theorem restrictSubmodule_definingIdealOfHom_resLE (i : Z ⟶ X) (V : X.Opens) :
    restrictSubmodule V (definingIdealOfHom i)
      = definingIdealOfHom (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  refine eq_definingIdealOfHom_of_mem_iff (i.resLE V (i ⁻¹ᵁ V) le_rfl) _ fun W s => ?_
  show ((i.app (V.ι ''ᵁ W)).hom s = 0) ↔
    (((i.resLE V (i ⁻¹ᵁ V) le_rfl).app W).hom s = 0)
  have happ : (i.resLE V (i ⁻¹ᵁ V) le_rfl).app W
      = i.app (V.ι ''ᵁ W) ≫ Z.presheaf.map (eqToHom (image_preimage_resLE i V W)).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE i le_rfl W _ le_rfl]
    exact congrArg (fun g => i.app (V.ι ''ᵁ W) ≫ Z.presheaf.map (op g))
      (Subsingleton.elim _ _)
  have hinj : Function.Injective (ConcreteCategory.hom
      (Z.presheaf.map (eqToHom (image_preimage_resLE i V W)).op)) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  have val : ((i.resLE V (i ⁻¹ᵁ V) le_rfl).app W).hom s
      = (Z.presheaf.map (eqToHom (image_preimage_resLE i V W)).op).hom
          ((i.app (V.ι ''ᵁ W)).hom s) := by
    rw [happ]; rfl
  exact ((iff_of_eq (congrArg (· = 0) val)).trans (map_eq_zero_iff _ hinj)).symm

/-- **The canonical open of a restricted immersion is cut out by the canonical open of the
original one.** A point of `V` lies in the canonical open of `i.resLE V (i ⁻¹ᵁ V) le_rfl`
exactly when it lies in the canonical open of `i`: the image of the restriction is the part of
the image lying in `V`, and `V` is open, so taking closures commutes with cutting down to
`V`. -/
theorem mem_coborderRange_resLE_iff (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
    (y : V.toScheme) :
    y ∈ (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange ↔ y.1 ∈ i.coborderRange := by
  have hr : Set.range (i.resLE V (i ⁻¹ᵁ V) le_rfl).base
      = Subtype.val ⁻¹' Set.range i.base := by
    ext w
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, (Scheme.Hom.coe_resLE_apply i le_rfl z).symm⟩
    · rintro ⟨z, hz⟩
      refine ⟨⟨z, show i.base z ∈ V from hz ▸ w.2⟩, ?_⟩
      exact Subtype.ext ((Scheme.Hom.coe_resLE_apply i le_rfl _).trans hz)
  have hclos : closure (Set.range (i.resLE V (i ⁻¹ᵁ V) le_rfl).base)
      = Subtype.val ⁻¹' closure (Set.range i.base) := by
    rw [hr]
    exact ((V.2.isOpenEmbedding_subtypeVal.isOpenMap).preimage_closure_eq_closure_preimage
      continuous_subtype_val _).symm
  show y ∈ coborder (Set.range (i.resLE V (i ⁻¹ᵁ V) le_rfl).base) ↔
    y.1 ∈ coborder (Set.range i.base)
  rw [mem_coborder_iff_imp, mem_coborder_iff_imp, hclos, hr]
  rfl

/-- The canonical open of `i.resLE V (i ⁻¹ᵁ V) le_rfl`, read as an open of `X`, is
`V ⊓ i.coborderRange`. -/
theorem imOpen_coborderRange_resLE (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) :
    imOpen V (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange = V ⊓ i.coborderRange := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, (mem_coborderRange_resLE_iff i V z).mp hz⟩
  · rintro ⟨hyV, hyC⟩
    exact ⟨⟨y, hyV⟩, (mem_coborderRange_resLE_iff i V ⟨y, hyV⟩).mpr hyC, rfl⟩

/-- A witness condition that survives shrinking the open passes from `i.coborderRange` to the
canonical open of a restriction of `i`, read on `X`. -/
private theorem hasWitnessIn_coborderRange_resLE (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
    {Q : ∀ (U : X.Opens) (r : ℕ), (Fin r → X.presheaf.obj (op U)) → Prop}
    (h : HasWitnessIn i.coborderRange (definingIdealOfHom i) Q)
    (hQ : ∀ {U : X.Opens} {r : ℕ} {f : Fin r → X.presheaf.obj (op U)} (U' : X.Opens)
      (hU' : U' ≤ U), Q U r f → Q U' r (fun k => X.presheaf.map (homOfLE hU').op (f k))) :
    HasWitnessIn (imOpen V (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange) (definingIdealOfHom i) Q :=
  hasWitnessIn_mono _ hQ (fun _ _ hy => (le_of_eq (imOpen_coborderRange_resLE i V) hy).2) h

/-- **Stacks tag 063J, part (2): Koszul-regularity survives restricting the target to an
open.** If `i : Z ⟶ X` is a Koszul-regular immersion then so is its restriction
`i.resLE V (i ⁻¹ᵁ V) le_rfl : i ⁻¹ᵁ V ⟶ V` to any open `V ⊆ X`. -/
@[stacks 063J "part (2): stability under restricting the target to an open"]
theorem isKoszulRegularImmersion_resLE (i : Z ⟶ X) [IsImmersion i]
    (h : IsKoszulRegularImmersion i) (V : X.Opens) :
    IsKoszulRegularImmersion (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  have hX := (isKoszulRegularIdealSheaf_restrictSubmodule_iff i.coborderRange
      (definingIdealOfHom i)).mp
    ((isKoszulRegularImmersion_iff i _
      (restrictSubmodule_coborderRange_definingIdealOfHom i)).mp h)
  refine (isKoszulRegularImmersion_iff (i.resLE V (i ⁻¹ᵁ V) le_rfl) _
    (restrictSubmodule_coborderRange_definingIdealOfHom _)).mpr ?_
  rw [← restrictSubmodule_definingIdealOfHom_resLE i V]
  exact (isKoszulRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V
    (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange (definingIdealOfHom i)).mpr
    (hasWitnessIn_coborderRange_resLE i V hX fun U' hU' hK => hK.of_le U' hU')

/-- **Stacks tag 063J, part (3): `H₁`-regularity survives restricting the target to an
open.** -/
@[stacks 063J "part (3): stability under restricting the target to an open"]
theorem isH1RegularImmersion_resLE (i : Z ⟶ X) [IsImmersion i]
    (h : IsH1RegularImmersion i) (V : X.Opens) :
    IsH1RegularImmersion (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  have hX := (isH1RegularIdealSheaf_restrictSubmodule_iff i.coborderRange
      (definingIdealOfHom i)).mp
    ((isH1RegularImmersion_iff i _
      (restrictSubmodule_coborderRange_definingIdealOfHom i)).mp h)
  refine (isH1RegularImmersion_iff (i.resLE V (i ⁻¹ᵁ V) le_rfl) _
    (restrictSubmodule_coborderRange_definingIdealOfHom _)).mpr ?_
  rw [← restrictSubmodule_definingIdealOfHom_resLE i V]
  exact (isH1RegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V
    (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange (definingIdealOfHom i)).mpr
    (hasWitnessIn_coborderRange_resLE i V hX fun U' hU' hK => hK.of_le U' hU')

/-- **Stacks tag 063J, part (4): quasi-regularity survives restricting the target to an
open.** -/
@[stacks 063J "part (4): stability under restricting the target to an open"]
theorem isQuasiRegularImmersion_resLE (i : Z ⟶ X) [IsImmersion i]
    (h : IsQuasiRegularImmersion i) (V : X.Opens) :
    IsQuasiRegularImmersion (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  have hX := (isQuasiRegularIdealSheaf_restrictSubmodule_iff i.coborderRange
      (definingIdealOfHom i)).mp
    ((isQuasiRegularImmersion_iff i _
      (restrictSubmodule_coborderRange_definingIdealOfHom i)).mp h)
  refine (isQuasiRegularImmersion_iff (i.resLE V (i ⁻¹ᵁ V) le_rfl) _
    (restrictSubmodule_coborderRange_definingIdealOfHom _)).mpr ?_
  rw [← restrictSubmodule_definingIdealOfHom_resLE i V]
  exact (isQuasiRegularIdealSheaf_restrictSubmodule_restrictSubmodule_iff V
    (i.resLE V (i ⁻¹ᵁ V) le_rfl).coborderRange (definingIdealOfHom i)).mpr
    (hasWitnessIn_coborderRange_resLE i V hX fun U' hU' hQ =>
      isQuasiRegularMap_isIso_of_le hQ U' hU')

end Immersion

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
