module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionColimit

/-!
# The terms of the twisted section sequence are the twisted global sections

`Stacks.SheafOfModules.twistedSectionSequence` is the `ℕ`-indexed system whose colimit is, by
`Stacks.SheafOfModules.isColimitTwistedSectionCocone`, the sections of a quasi-coherent module on
the nonvanishing open of a global section `s` of an invertible module `L`. Its `n`-th term is
*defined* as the degree-`n * 1` homogeneous piece
`Stacks.SheafOfModules.sectionModuleGrading` of the graded section module, which is the range of
`DirectSum.of` -- a subgroup of a direct sum, not the group of twisted global sections
`Γ(X, H ⊗ L^{⊗ n})` that the colimit statement is read with.

The `n`-th term is identified with `Γ(X, H ⊗ L^{⊗ n})`, and under that identification the
transition map from the `n`-th to the `(n+1)`-st term is multiplication by `s`.

## Main definitions

* `Stacks.SheafOfModules.ofRangeEquivOfEq`: **the range of one inclusion into a direct sum is that
  summand**, read off at any index equal to the one included.
* `Stacks.SheafOfModules.twistedSectionDegreeEquiv`: the degree-`j` piece of the graded section
  module is `Γ(X, H ⊗ L^{⊗ k})` for any `k = j`.
* `Stacks.SheafOfModules.twistedSectionSequenceObjEquiv` and
  `Stacks.SheafOfModules.twistedSectionSequenceObjIso`: **the `n`-th term of
  `Stacks.SheafOfModules.twistedSectionSequence` is `Γ(X, H ⊗ L^{⊗ n})`**, as an additive
  equivalence and as an isomorphism of `AddCommGrpCat`.
* `Stacks.SheafOfModules.smulTwistHom` and `Stacks.SheafOfModules.mulBySectionHom`:
  **multiplication by the global section `s`** on twisted global sections, raising the twist from
  `n` to `n + 1`.

## Main results

* `Stacks.SheafOfModules.twistedSectionSequence_obj`: the `n`-th term is the degree-`n * 1` piece
  of the graded section module, by definition.
* `Stacks.SheafOfModules.homogeneousSection_smul_of`: acting by the degree-one homogeneous element
  attached to `s` on a homogeneous element of the section module is the graded action of
  [Stacks, Tag 01CV].
* `Stacks.SheafOfModules.subtype_twistedSectionSequence_map_succ`: the transition map is
  multiplication by that element, on the underlying elements of the graded section module.
* `Stacks.SheafOfModules.of_twistedSectionSequence_map_succ`: compared inside the graded section
  module, the transition map from the `n`-th to the `(n+1)`-st term sends a twisted global section
  `a` of `H ⊗ L^{⊗ n}` to the graded action of `s` on `a`.
* `Stacks.SheafOfModules.twistedSectionSequenceObjEquiv_map_succ`: under the identification of the
  terms with twisted global sections, the transition map is multiplication by `s`.
* `Stacks.SheafOfModules.twistedSectionSequenceObjIso_naturality`: the same as a commuting square
  in `AddCommGrpCat`, with multiplication by `s` as the right-hand edge.

## Implementation notes

The homogeneous pieces of the section module are the ranges of the structure maps of the direct
sum (`Stacks.SheafOfModules.sectionModuleGrading`), so the identification is elementary: an
element of the range is the inclusion of a unique summand element, and the equivalence reads off
that coordinate. The only friction is the degree bookkeeping. The `n`-th term of
`Stacks.SheafOfModules.homogeneousSequence` sits in degree `n * d` at the degree `d` of the
homogeneous element, which is `n * 1` here, and the graded action of a degree-one element on
degree `j` lands in degree `1 + j`; neither `n * 1` nor `1 + n` is the literal `n`, resp. `n + 1`,
that the twisted sections are indexed by. So `Stacks.SheafOfModules.ofRangeEquivOfEq` carries an
equality of indices, and `Stacks.SheafOfModules.twistCastEquiv` is the transport of twisted global
sections along an equality of twisting exponents -- the identity on the underlying section, since
the two groups are the same group.

Multiplication by `s` is the graded action `Stacks.SheafOfModules.sectionModuleAction` of
[Stacks, Tag 01CV] by `Stacks.SheafOfModules.sectionPower X L s 1`, which
`Stacks.SheafOfModules.sectionPower_one` identifies with `s` itself under `L^{⊗ 1} ≅ L`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/


@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits

universe u

/-! ### One summand of a direct sum, as the range of its inclusion -/

/-- **The range of the `i`-th inclusion into a direct sum is the `i`-th summand**, read off at any
index `j` equal to `i`: an element of the range is the inclusion of a unique summand element, and
the equivalence takes the `j`-th coordinate. -/
public def ofRangeEquivOfEq {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] {i j : ι} (h : i = j) :
    ((DirectSum.of A i).range) ≃+ A j where
  toFun x := (x : ⨁ i, A i) j
  invFun a := ⟨DirectSum.of A j a, by subst h; exact ⟨a, rfl⟩⟩
  left_inv x := by
    refine Subtype.ext ?_
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp x.2
    subst h
    change DirectSum.of A i ((x : ⨁ i, A i) i) = (x : ⨁ i, A i)
    rw [← ha, DirectSum.of_eq_same]
  right_inv a := DirectSum.of_eq_same j a
  map_add' x y := rfl

/-- Including the coordinate read off by `Stacks.SheafOfModules.ofRangeEquivOfEq` recovers the
element of the range. -/
public theorem of_ofRangeEquivOfEq {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] {i j : ι} (h : i = j) (x : (DirectSum.of A i).range) :
    DirectSum.of A j (ofRangeEquivOfEq A h x) = (x : ⨁ i, A i) := by
  change DirectSum.of A j ((x : ⨁ i, A i) j) = (x : ⨁ i, A i)
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp x.2
  subst h
  rw [← ha, DirectSum.of_eq_same]

section TwistedSectionTerms

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule
  Stacks.SheafOfModules.sectionModuleDecompositionColim
  Stacks.SheafOfModules.sectionModuleGradedSMulColim

variable (H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-! ### The homogeneous pieces of the graded section module -/

/-- **The degree-`j` homogeneous piece of the graded section module is the group of twisted global
sections `Γ(X, H ⊗ L^{⊗ k})`** for any twisting exponent `k` equal to `j`. -/
public def twistedSectionDegreeEquiv (j k : ℤ) (h : j = k) :
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H j) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L k)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  ofRangeEquivOfEq
    (fun m : ℤ => ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L m)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) h

/-- Placing the twisted global section underlying a homogeneous element back in its degree
recovers the element. -/
public theorem of_twistedSectionDegreeEquiv (j k : ℤ) (h : j = k)
    (x : sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H j) :
    (DirectSum.of _ k (twistedSectionDegreeEquiv X L H j k h x) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      (x : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) :=
  of_ofRangeEquivOfEq _ h x

/-- Twisted global sections at equal twisting exponents are the same group, and the transport
between them is the identity on the underlying section. -/
public def twistCastEquiv {j k : ℤ} (h : j = k) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L k)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) := by
  subst h
  exact AddEquiv.refl _

/-- The transport of `Stacks.SheafOfModules.twistCastEquiv` does not move the homogeneous element
of the section module, only the degree it is recorded in. -/
public theorem of_twistCastEquiv {j k : ℤ} (h : j = k)
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ k (twistCastEquiv X L H h a) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) = DirectSum.of _ j a := by
  subst h
  rfl

/-! ### Multiplication by the global section -/

/-- Acting by the degree-one homogeneous element attached to `s` on a homogeneous element of the
section module is the graded action of [Stacks, Tag 01CV] by the degree-one section
`Stacks.SheafOfModules.sectionPower X L s 1`, in degree `1 + j`. -/
public theorem homogeneousSection_smul_of (s : L.sections) (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    homogeneousSection X L s • (DirectSum.of _ j t :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      DirectSum.of _ (((1 : ℕ) : ℤ) + j)
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H 1 j
          (sectionPower X L s 1) t) := by
  refine Eq.trans (congrArg (fun c => c • (DirectSum.of _ j t :
    sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H))
    ((pow_one (homogeneousSection X L s)).symm.trans
      (homogeneousSection_pow_eq_of_sectionPower X L s 1))) ?_
  exact (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L H).smul_eq 1 j
    (sectionPower X L s 1) t

/-- The graded action of [Stacks, Tag 01CV] is additive in the twisted section it acts on. -/
public theorem sectionModuleAction_add_section (n : ℕ) (j : ℤ)
    (σ : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (t₁ t₂ : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H n j σ (t₁ + t₂) =
      sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H n j σ t₁ +
        sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H n j σ t₂ := by
  unfold sectionModuleAction
  exact (congrArg _ (tensorGlobalSection_add_right (sectionSiteRing X) (sectionSiteSheaf X)
    _ _ σ t₁ t₂)).trans (map_add _ _ _)

/-- **Multiplication by the global section `s`** on twisted global sections, as an additive map
`Γ(X, H ⊗ L^{⊗ j}) →+ Γ(X, H ⊗ L^{⊗ (1 + j)})`: the graded action of [Stacks, Tag 01CV] by the
degree-one section `Stacks.SheafOfModules.sectionPower X L s 1` carrying `s`. -/
public def smulTwistHom (s : L.sections) (j : ℤ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) →+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          (((1 : ℕ) : ℤ) + j))))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  AddMonoidHom.mk'
    (fun a => sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H 1 j
      (sectionPower X L s 1) a)
    (sectionModuleAction_add_section X L H 1 j (sectionPower X L s 1))

/-- **Multiplication by the global section `s`**, raising the twist from `n` to `n + 1`:
`Γ(X, H ⊗ L^{⊗ n}) →+ Γ(X, H ⊗ L^{⊗ (n + 1)})`. -/
public def mulBySectionHom (s : L.sections) (n : ℕ) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          (n : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) →+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          ((n + 1 : ℕ) : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  (twistCastEquiv X L H
      (by push_cast; ring :
        ((1 : ℕ) : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ))).toAddMonoidHom.comp
    (smulTwistHom X L H s (n : ℤ))

/-! ### The terms of the twisted section sequence -/

/-- The `n`-th term of `Stacks.SheafOfModules.twistedSectionSequence` is, by definition, the
degree-`n * 1` homogeneous piece of the graded section module. -/
public theorem twistedSectionSequence_obj (s : L.sections) (n : ℕ) :
    (twistedSectionSequence X L H s).obj n =
      AddCommGrpCat.of (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H
        ((n * 1 : ℕ) : ℤ)) := rfl

/-- **The `n`-th term of the twisted section sequence is the group of twisted global sections
`Γ(X, H ⊗ L^{⊗ n})`.** -/
public def twistedSectionSequenceObjEquiv (s : L.sections) (n : ℕ) :
    ((twistedSectionSequence X L H s).obj n) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          (n : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  twistedSectionDegreeEquiv X L H ((n * 1 : ℕ) : ℤ) (n : ℤ) (by simp)

/-- **The `n`-th term of the twisted section sequence is the group of twisted global sections
`Γ(X, H ⊗ L^{⊗ n})`**, as an isomorphism of `AddCommGrpCat`. -/
public def twistedSectionSequenceObjIso (s : L.sections) (n : ℕ) :
    (twistedSectionSequence X L H s).obj n ≅
      AddCommGrpCat.of (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          (n : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :=
  AddEquiv.toAddCommGrpIso (twistedSectionSequenceObjEquiv X L H s n)

/-- The homogeneous element of the graded section module underlying a term of the twisted section
sequence: the inclusion of the degree-`n * 1` piece, read at the sequence's own `n`-th term. -/
public def twistedSectionSequenceSubtype (s : L.sections) (n : ℕ) :
    ((twistedSectionSequence X L H s).obj n) →+
      sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H :=
  (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H ((n * 1 : ℕ) : ℤ)).subtype

/-- Placing the twisted global section underlying a term of the sequence back in degree `n`
recovers the term. -/
public theorem of_twistedSectionSequenceObjEquiv (s : L.sections) (n : ℕ)
    (x : (twistedSectionSequence X L H s).obj n) :
    (DirectSum.of _ (n : ℤ) (twistedSectionSequenceObjEquiv X L H s n x) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      twistedSectionSequenceSubtype X L H s n x :=
  of_twistedSectionDegreeEquiv X L H ((n * 1 : ℕ) : ℤ) (n : ℤ) (by simp) x

/-- **The transition map of the twisted section sequence is multiplication by `s`**, read on the
underlying homogeneous elements of the graded section module: it is the action of the degree-one
element `Stacks.SheafOfModules.homogeneousSection X L s`. -/
public theorem subtype_twistedSectionSequence_map_succ (s : L.sections) (n : ℕ)
    (x : (twistedSectionSequence X L H s).obj n) :
    twistedSectionSequenceSubtype X L H s (n + 1)
        ((twistedSectionSequence X L H s).map (homOfLE (Nat.le_add_right n 1)) x) =
      homogeneousSection X L s • twistedSectionSequenceSubtype X L H s n x :=
  (congrArg
      (fun φ : (twistedSectionSequence X L H s).obj n ⟶
          (twistedSectionSequence X L H s).obj (n + 1) =>
        twistedSectionSequenceSubtype X L H s (n + 1) (φ x))
      (homogeneousSequence_map_succ
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
        (homogeneousSection_mem X L s) n)).trans
    (coe_homogeneousSmulHom (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
      (homogeneousSection_mem X L s) n x)

/-- Under the identification of the `n`-th term of `Stacks.SheafOfModules.twistedSectionSequence`
with the twisted global sections `Γ(X, H ⊗ L^{⊗ n})`, the transition map to the `(n+1)`-st term
sends a twisted global section `a` of `H ⊗ L^{⊗ n}` to the graded action of `s` on `a`, a twisted
global section of `H ⊗ L^{⊗ (1 + n)}`. The two sides are placed in the graded section module,
where the equal degrees `n + 1` and `1 + n` need no transport. -/
public theorem of_twistedSectionSequence_map_succ (s : L.sections) (n : ℕ)
    (x : (twistedSectionSequence X L H s).obj n) :
    (DirectSum.of _ ((n + 1 : ℕ) : ℤ)
        (twistedSectionSequenceObjEquiv X L H s (n + 1)
          ((twistedSectionSequence X L H s).map (homOfLE (Nat.le_add_right n 1)) x)) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      DirectSum.of _ (((1 : ℕ) : ℤ) + (n : ℤ))
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H 1 (n : ℤ)
          (sectionPower X L s 1) (twistedSectionSequenceObjEquiv X L H s n x)) :=
  ((of_twistedSectionSequenceObjEquiv X L H s (n + 1)
        ((twistedSectionSequence X L H s).map (homOfLE (Nat.le_add_right n 1)) x)).trans
      ((subtype_twistedSectionSequence_map_succ X L H s n x).trans
        (congrArg (fun y => homogeneousSection X L s • y)
          (of_twistedSectionSequenceObjEquiv X L H s n x).symm))).trans
    (homogeneousSection_smul_of X L H s (n : ℤ) (twistedSectionSequenceObjEquiv X L H s n x))

/-- Under the identification of the terms of `Stacks.SheafOfModules.twistedSectionSequence` with
the twisted global sections, the transition map from the `n`-th to the `(n+1)`-st term is
multiplication by the global section `s`. -/
public theorem twistedSectionSequenceObjEquiv_map_succ (s : L.sections) (n : ℕ)
    (x : (twistedSectionSequence X L H s).obj n) :
    twistedSectionSequenceObjEquiv X L H s (n + 1)
        ((twistedSectionSequence X L H s).map (homOfLE (Nat.le_add_right n 1)) x) =
      mulBySectionHom X L H s n (twistedSectionSequenceObjEquiv X L H s n x) :=
  DirectSum.of_injective
    (β := fun m : ℤ => ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
          (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (H)).obj
        ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L m)))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) ((n + 1 : ℕ) : ℤ)
    ((of_twistedSectionSequence_map_succ X L H s n x).trans
      (of_twistCastEquiv X L H
        (show ((1 : ℕ) : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by push_cast; ring)
        (smulTwistHom X L H s (n : ℤ)
          (twistedSectionSequenceObjEquiv X L H s n x))).symm)

/-- As a commuting square in `AddCommGrpCat`: the transition map of
`Stacks.SheafOfModules.twistedSectionSequence` from the `n`-th to the `(n+1)`-st term is, under
the identification of both terms with twisted global sections, multiplication by the global
section `s`. -/
public theorem twistedSectionSequenceObjIso_naturality (s : L.sections) (n : ℕ) :
    (twistedSectionSequence X L H s).map (homOfLE (Nat.le_add_right n 1)) ≫
        (twistedSectionSequenceObjIso X L H s (n + 1)).hom =
      (twistedSectionSequenceObjIso X L H s n).hom ≫
        AddCommGrpCat.ofHom (mulBySectionHom X L H s n) := by
  ext x
  exact twistedSectionSequenceObjEquiv_map_succ X L H s n x

end TwistedSectionTerms

end Stacks.SheafOfModules

end
