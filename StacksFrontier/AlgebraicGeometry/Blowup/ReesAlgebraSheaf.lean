module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent

/-!
# The Rees algebra of a quasi-coherent ideal sheaf

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, recorded by Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`.  This file constructs the *Rees algebra*
`⨁_{n ≥ 0} ℐⁿ` of `ℐ`: a sheaf of `ℤ`-graded, commutative, quasi-coherent `𝒪_X`-algebras
concentrated in nonnegative degrees, whose degree-`n` piece is `ℐⁿ` and whose multiplication
is the multiplication of `𝒪_X`.  This is the graded algebra whose relative `Proj` is the blowup
of `X` in `ℐ` (Stacks, Tag 01OG).

The construction is global: no affineness, quasi-compactness or noetherian hypothesis on `X`.
The degree-`n` piece is realized as the kernel of `𝒪_X ⟶ (ι_n)_* 𝒪_{V(ℐⁿ)}`, where `ι_n` is
the closed immersion of the subscheme cut out by `ℐⁿ`; quasi-coherence of that kernel is
Tag 01R8.  The identification of its sections over an affine open `U` with `ℐⁿ(U) = ℐ(U)ⁿ`
is the `pieceEquiv` field below.

## Main definitions

* `Stacks.Blowup.ReesAlgebraData`: the data of a sheaf of graded algebras on `X` together
  with the identification of its degree-`n` sections over an affine open `U` with `ℐ(U)ⁿ`,
  compatibly with scalars, multiplication, the unit and restriction.
* `Stacks.Blowup.reesPiece`, `Stacks.Blowup.reesMultiplication`, `Stacks.Blowup.reesUnit`
  and `Stacks.Blowup.reesGradedAlgebra`: the pieces, multiplication, unit and assembled
  graded algebra of `⨁_{n ≥ 0} ℐⁿ`.
* `Stacks.Blowup.reesAlgebraData`: the Rees algebra with its affine-local description.
* `Stacks.Blowup.reesSituation`: the Rees algebra packaged as a `Stacks.RelativeProj.Situation`,
  i.e. as input for relative `Proj`.

## Main results

* `Stacks.Blowup.exists_reesAlgebraData`: a graded sheaf with the canonical affine-local
  description of `⨁ₙ ℐⁿ` exists.

## Implementation notes

The homogeneous pieces are indexed by `ℤ`, with the negative pieces the zero sheaf (realized
as the free sheaf on `PEmpty`), because `SheafOfModules.GradedAlgebra` is `ℤ`-graded; that the
negative pieces vanish is the `negative_isZero` field.

All the structural identities — associativity, commutativity and the two unit laws — are proved
by transporting the question to the *ambient* sections: a section of `ℐⁿ` over `U` is sent to
its image in `Γ(X, U)` by `reesPieceAmbient`, this map is injective in nonnegative degrees
(`reesPieceAmbient_injective`), and it turns the graded multiplication into multiplication in
`Γ(X, U)` (`reesMultiplication_ambient`).  So each identity reduces to the corresponding
identity in the commutative ring `Γ(X, U)`.  The identities are stated with `HEq` because the
two sides live in pieces of propositionally — not definitionally — equal degree.

That a product of local sections of `ℐⁿ` and `ℐᵐ` again lies in `ℐⁿ⁺ᵐ`, and that `1` lies in
`ℐ⁰`, are local statements verified on affine opens and then glued by the sheaf property of the
target of `𝒪_X ⟶ (ι_{n+m})_* 𝒪_{V(ℐⁿ⁺ᵐ)}`; this is why `idealPowerKernel_product_quotient_eq_zero`
and `idealPowerZero_quotient_one` go through `TopCat.Presheaf.IsSheaf.section_ext` and the basis
of affine opens, rather than being checked on `U` directly.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Blowup

universe u

/-- The degree-`n` piece of the Rees algebra of `I`, for `n : ℕ`: the kernel of the map from
`𝒪_X` to the direct image of the structure sheaf of the subscheme cut out by `Iⁿ`. -/
public def idealPowerKernel {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom)

/-- The degree-`n` piece of the Rees algebra of `I`, for `n : ℤ`: it is `Iⁿ` for `n ≥ 0`
and zero for `n < 0`. -/
public def reesPiece {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ) :
    SheafOfModules.{u} X.ringCatSheaf :=
  match n with
  | .ofNat k => idealPowerKernel I k
  | .negSucc _ => SheafOfModules.free (R := X.ringCatSheaf) PEmpty

/-- The pieces of the Rees algebra in negative degrees vanish. -/
public theorem reesPiece_negative_isZero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : n < 0) : IsZero (reesPiece I n) := by
  cases n with
  | ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | negSucc k =>
    change IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty)
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact i.elim

/-- Over an affine open `U`, the kernel of `𝒪_X(U) ⟶ ((ι_J)_* 𝒪_{V(J)})(U)` is the ideal `J(U)`. -/
public theorem ker_unitToPushforwardObjUnit_app {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) :
    (ModuleCat.Hom.hom ((SheafOfModules.unitToPushforwardObjUnit
      J.subschemeι.toRingCatSheafHom).val.app (op U.1))).ker.toAddSubgroup =
      (J.ideal U).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  let xx : Γ(X, U.1) := x
  change ((forget₂ RingCat AddCommGrpCat).map
    ((J.subschemeι.toRingCatSheafHom).hom.app (op U.1)) x = 0) ↔ x ∈ J.ideal U
  change (J.subschemeι.app U).hom xx = 0 ↔ xx ∈ J.ideal U
  rw [← J.ker_subschemeι_app U, RingHom.mem_ker]

/-- Over an affine open `U`, the sections of the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` are the
ideal `J(U)`. -/
public def idealKernelSectionsEquiv {X : Scheme.{u}} (J : X.IdealSheafData) (U : X.affineOpens) :
    (kernel (SheafOfModules.unitToPushforwardObjUnit
      J.subschemeι.toRingCatSheafHom)).val.obj (op U.1) ≃+ ↥(J.ideal U) := by
  let f := SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U.1)
  have : PreservesLimitsOfSize.{0, 0} E := preservesLimitsOfSize_shrink _
  let e := PreservesKernel.iso E f
  let k := ModuleCat.kernelIsoKer (E.map f)
  let g : E.obj (kernel f) ⟶ ModuleCat.of _ (ModuleCat.Hom.hom (E.map f)).ker := e.hom ≫ k.hom
  let eg : E.obj (kernel f) ≃+ ↥(ModuleCat.Hom.hom (E.map f)).ker :=
    AddEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)
  exact eg.trans (AddEquiv.cast (M := fun H : AddSubgroup _ => H)
    (ker_unitToPushforwardObjUnit_app J U))

private theorem idealPowerKernel_isQuasicoherent {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (idealPowerKernel I n).IsQuasicoherent := by
  change (kernel (SheafOfModules.unitToPushforwardObjUnit
    (I ^ n).subschemeι.toRingCatSheafHom)).IsQuasicoherent
  infer_instance

/-- Over an affine open `U`, the degree-`n` sections of the Rees algebra of `I` are the
ideal `I(U)ⁿ`. -/
public def idealPowerKernelSectionsEquiv {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.affineOpens) : (idealPowerKernel I n).val.obj (op U.1) ≃+ ↥(I.ideal U ^ n) := by
  change (kernel (SheafOfModules.unitToPushforwardObjUnit
    (I ^ n).subschemeι.toRingCatSheafHom)).val.obj (op U.1) ≃+ ↥(I.ideal U ^ n)
  exact (idealKernelSectionsEquiv (I ^ n) U).trans
    (AddEquiv.cast (M := fun K : Ideal Γ(X, U.1) => ↥K)
      (by simp [Scheme.IdealSheafData.ideal_pow]))

private theorem addSubgroup_cast_coe {α : Type*} [AddGroup α] {A B : AddSubgroup α} (h : A = B)
    (x : A) : ((cast (congrArg (fun H : AddSubgroup α => ↥H) h) x : B) : α) = x := by
  cases h
  rfl

/-- The identification of `E (kernel f)` with `ker (E f)` is compatible with `E (kernel.ι f)`. -/
private theorem preservesKernel_kernelIsoKer_coe {C : Type*} [Category C] [HasZeroMorphisms C]
    {R : Type*} [Ring R] (E : C ⥤ ModuleCat R) {A B : C} (f : A ⟶ B) [HasKernel f]
    [E.PreservesZeroMorphisms] [PreservesLimit (parallelPair f 0) E] (x : E.obj (kernel f)) :
    (((PreservesKernel.iso E f).hom ≫ (ModuleCat.kernelIsoKer (E.map f)).hom).hom x :
      E.obj A) = (E.map (kernel.ι f)).hom x := by
  have he : (PreservesKernel.iso E f).hom ≫ kernel.ι (E.map f) = E.map (kernel.ι f) :=
    ((Iso.inv_comp_eq _).mp (PreservesKernel.iso_inv_ι (G := E) f)).symm
  have hg : ((PreservesKernel.iso E f).hom ≫ (ModuleCat.kernelIsoKer (E.map f)).hom) ≫
      ModuleCat.ofHom (E.map f).hom.ker.subtype = E.map (kernel.ι f) := by
    rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype, he]
  exact congrArg (fun q => q.hom x) hg

private theorem idealPowerKernelSectionsEquiv_coe {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.affineOpens) (x : (idealPowerKernel I n).val.obj (op U.1)) :
    ((idealPowerKernelSectionsEquiv I n U x : ↥(I.ideal U ^ n)) : Γ(X, U.1)) =
      ConcreteCategory.hom
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U.1)) x := by
  let J := I ^ n
  let f := SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U.1)
  have : PreservesLimitsOfSize.{0, 0} E := preservesLimitsOfSize_shrink _
  let e := PreservesKernel.iso E f
  let k := ModuleCat.kernelIsoKer (E.map f)
  have hker : (ModuleCat.Hom.hom (E.map f)).ker.toAddSubgroup = (J.ideal U).toAddSubgroup :=
    ker_unitToPushforwardObjUnit_app J U
  let g : E.obj (kernel f) ⟶ ModuleCat.of _ (ModuleCat.Hom.hom (E.map f)).ker := e.hom ≫ k.hom
  let eg : E.obj (kernel f) ≃+ ↥(ModuleCat.Hom.hom (E.map f)).ker :=
    AddEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)
  let toΓ : ↑(E.obj (SheafOfModules.unit X.ringCatSheaf)) → Γ(X, U.1) := fun z => z
  have hcast (z : ↥(ModuleCat.Hom.hom (E.map f)).ker) :
      toΓ ((AddEquiv.cast (M := fun H : AddSubgroup _ => ↥H) hker
        (z : ↥(ModuleCat.Hom.hom (E.map f)).ker.toAddSubgroup) :
          ↥(J.ideal U).toAddSubgroup) : ↑(E.obj (SheafOfModules.unit X.ringCatSheaf))) =
        toΓ (z : ↑(E.obj (SheafOfModules.unit X.ringCatSheaf))) :=
    congrArg toΓ (addSubgroup_cast_coe hker _)
  change toΓ ((AddEquiv.cast (M := fun H : AddSubgroup _ => ↥H) hker
    (eg x : ↥(ModuleCat.Hom.hom (E.map f)).ker.toAddSubgroup) :
      ↥(J.ideal U).toAddSubgroup) : ↑(E.obj (SheafOfModules.unit X.ringCatSheaf))) = _
  rw [hcast]
  change toΓ ((Subtype.val ∘ g.hom) x) = _
  exact congrArg toΓ (preservesKernel_kernelIsoKer_coe E f x)

/-- A section of the sheaf of rings `X.ringCatSheaf`, read as a section of `𝒪_X`.  The two
types have the same carrier, but only after unfolding `Scheme.ringCatSheaf`; naming the
identification keeps it out of the statements that mention both. -/
public def ringSectionToGamma {X : Scheme.{u}} {U : X.Opens}
    (r : X.ringCatSheaf.obj.obj (op U)) : Γ(X, U) := r

/-- The image in `Γ(X, U)` of a section of the degree-`n` piece of the Rees algebra. -/
public def idealPowerKernelAmbient {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (U : X.Opens)
    (x : (idealPowerKernel I n).val.obj (op U)) : Γ(X, U) :=
  ConcreteCategory.hom
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U)) x

private theorem idealPowerKernelAmbient_zero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) : idealPowerKernelAmbient I n U 0 = 0 :=
  ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U)).hom.map_zero

private theorem idealPowerKernelAmbient_add {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) (x y : (idealPowerKernel I n).val.obj (op U)) :
    idealPowerKernelAmbient I n U (x + y) =
      idealPowerKernelAmbient I n U x + idealPowerKernelAmbient I n U y :=
  ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U)).hom.map_add x y

private theorem idealPowerKernelAmbient_smul {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U))
    (x : (idealPowerKernel I n).val.obj (op U)) :
    idealPowerKernelAmbient I n U (r • x) =
      ringSectionToGamma r * idealPowerKernelAmbient I n U x :=
  ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U)).hom.map_smul r x

private theorem idealPowerKernelAmbient_restrict {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U V : X.Opens) (h : U ≤ V) (x : (idealPowerKernel I n).val.obj (op V)) :
    idealPowerKernelAmbient I n U
        (ConcreteCategory.hom ((idealPowerKernel I n).val.map (homOfLE h).op) x) =
      X.presheaf.map (homOfLE h).op (idealPowerKernelAmbient I n V x) := by
  change ConcreteCategory.hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (I ^ n).subschemeι.toRingCatSheafHom)).val.app (op U))
        (ConcreteCategory.hom ((idealPowerKernel I n).val.map (homOfLE h).op) x) = _
  exact PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (I ^ n).subschemeι.toRingCatSheafHom)).val (homOfLE h).op x

private theorem idealPowerKernelAmbient_mem_affine {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.affineOpens) (x : (idealPowerKernel I n).val.obj (op U.1)) :
    idealPowerKernelAmbient I n U.1 x ∈ I.ideal U ^ n := by
  rw [idealPowerKernelAmbient, ← idealPowerKernelSectionsEquiv_coe I n U x]
  exact (idealPowerKernelSectionsEquiv I n U x).property

/-- A section of `𝒪_X` over `U` whose restriction to every affine open `V ⊆ U` lies in `J(V)`
is killed by `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}`. -/
public theorem unitToPushforwardObjUnit_app_eq_zero_of_forall_affine {X : Scheme.{u}}
    (J : X.IdealSheafData) (U : X.Opens) (s : Γ(X, U))
    (hs : ∀ (V : X.affineOpens) (h : V.1 ≤ U), X.presheaf.map (homOfLE h).op s ∈ J.ideal V) :
    ((SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom).val.app
      (op U)).hom s = 0 := by
  let q := SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom
  let Q := (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit J.subscheme.ringCatSheaf)
  apply TopCat.Presheaf.IsSheaf.section_ext (U := op U) Q.isSheaf
  intro z hz
  obtain ⟨V, ⟨V₀, hV₀, rfl⟩, hzV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz U.2
  let V : X.affineOpens := ⟨V₀, hV₀⟩
  have h : V.1 ≤ U := hVU
  let f := (homOfLE h).op
  have hqV : (q.val.app (op V.1)).hom (X.presheaf.map f s) = 0 := by
    change (J.subschemeι.app V.1).hom (X.presheaf.map f s) = 0
    rw [← RingHom.mem_ker, J.ker_subschemeι_app V]
    exact hs V h
  refine ⟨V.1, h, hzV, ?_⟩
  change ConcreteCategory.hom (Q.val.map f) ((q.val.app (op U)).hom s) =
    ConcreteCategory.hom (Q.val.map f) 0
  have hnat : ConcreteCategory.hom (Q.val.map f) ((q.val.app (op U)).hom s) =
      (q.val.app (op V.1)).hom (X.presheaf.map f s) :=
    (PresheafOfModules.naturality_apply q.val f _).symm
  rw [hnat, hqV, map_zero]
  rfl

/-- The product of a local section of `Iⁿ` and a local section of `Iᵐ` is killed by
`𝒪_X ⟶ (ι_{n+m})_* 𝒪_{V(Iⁿ⁺ᵐ)}`, i.e. it lies in `Iⁿ⁺ᵐ`. -/
public theorem idealPowerKernel_product_quotient_eq_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) (U : X.Opens) (x : (idealPowerKernel I n).val.obj (op U))
    (y : (idealPowerKernel I m).val.obj (op U)) :
    (((SheafOfModules.unitToPushforwardObjUnit
      (I ^ (n + m)).subschemeι.toRingCatSheafHom).val.app (op U)).hom
      (idealPowerKernelAmbient I n U x * idealPowerKernelAmbient I m U y)) = 0 :=
  unitToPushforwardObjUnit_app_eq_zero_of_forall_affine (I ^ (n + m)) U
    (idealPowerKernelAmbient I n U x * idealPowerKernelAmbient I m U y) fun V h => by
    rw [map_mul, ← idealPowerKernelAmbient_restrict I n V.1 U h x,
      ← idealPowerKernelAmbient_restrict I m V.1 U h y]
    change _ ∈ I.ideal V ^ (n + m)
    rw [pow_add]
    exact Ideal.mul_mem_mul (idealPowerKernelAmbient_mem_affine I n V _)
      (idealPowerKernelAmbient_mem_affine I m V _)

/-- Over any open `U`, the degree-`n` sections of the Rees algebra are the kernel of the
map on sections of `𝒪_X ⟶ (ι_n)_* 𝒪_{V(Iⁿ)}`. -/
public def idealPowerKernelSubmoduleEquiv {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) :
    (idealPowerKernel I n).val.obj (op U) ≃+
      ↥((ModuleCat.Hom.hom ((SheafOfModules.unitToPushforwardObjUnit
        (I ^ n).subschemeι.toRingCatSheafHom).val.app (op U))).ker) := by
  let f := SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  have : PreservesLimitsOfSize.{0, 0} E := preservesLimitsOfSize_shrink _
  let e := PreservesKernel.iso E f
  let k := ModuleCat.kernelIsoKer (E.map f)
  let g : E.obj (kernel f) ⟶ ModuleCat.of _ (ModuleCat.Hom.hom (E.map f)).ker := e.hom ≫ k.hom
  exact AddEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)

private theorem idealPowerKernelSubmoduleEquiv_coe {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) (x : (idealPowerKernel I n).val.obj (op U)) :
    (idealPowerKernelSubmoduleEquiv I n U x :
      (SheafOfModules.unit X.ringCatSheaf).val.obj (op U)) =
      idealPowerKernelAmbient I n U x := by
  let f := SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  have : PreservesLimitsOfSize.{0, 0} E := preservesLimitsOfSize_shrink _
  exact preservesKernel_kernelIsoKer_coe E f x

private theorem idealPowerKernelAmbient_injective {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (U : X.Opens) : Function.Injective (idealPowerKernelAmbient I n U) := fun x y h =>
  (idealPowerKernelSubmoduleEquiv I n U).injective <| Subtype.ext <|
    (idealPowerKernelSubmoduleEquiv_coe I n U x).trans
      (h.trans (idealPowerKernelSubmoduleEquiv_coe I n U y).symm)

/-- The unit section of `𝒪_X` over `U`, read in `SheafOfModules.unit X.ringCatSheaf`. -/
public def unitOne {X : Scheme.{u}} (U : X.Opens) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj (op U) :=
  (1 : X.ringCatSheaf.obj.obj (op U))

/-- The unit section of `𝒪_X` is killed by `𝒪_X ⟶ (ι_0)_* 𝒪_{V(I⁰)}`, i.e. it lies in
`I⁰ = 𝒪_X`. -/
public theorem idealPowerZero_quotient_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) :
    (((SheafOfModules.unitToPushforwardObjUnit
      (I ^ 0).subschemeι.toRingCatSheafHom).val.app (op U)).hom) (unitOne U) = 0 :=
  unitToPushforwardObjUnit_app_eq_zero_of_forall_affine (I ^ 0) U (1 : Γ(X, U)) fun V h => by
    rw [map_one]
    change (1 : Γ(X, V.1)) ∈ I.ideal V ^ 0
    simp

/-- The section of the degree-zero piece `I⁰ = 𝒪_X` over `U` given by `1`. -/
public def idealPowerKernelOneAt {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    (idealPowerKernel I 0).val.obj (op U) :=
  (idealPowerKernelSubmoduleEquiv I 0 U).symm ⟨unitOne U, idealPowerZero_quotient_one I U⟩

private theorem idealPowerKernelOneAt_ambient {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) : idealPowerKernelAmbient I 0 U (idealPowerKernelOneAt I U) = 1 := by
  rw [← idealPowerKernelSubmoduleEquiv_coe I 0 U, idealPowerKernelOneAt,
    (idealPowerKernelSubmoduleEquiv I 0 U).apply_symm_apply]
  rfl

/-- The unit of the Rees algebra: the global section `1` of the degree-zero piece. -/
public def reesUnit {X : Scheme.{u}} (I : X.IdealSheafData) :
    (idealPowerKernel I 0).val.sections :=
  (idealPowerKernel I 0).val.sectionsMk (fun U => idealPowerKernelOneAt I U.unop) (by
    intro U V f
    apply idealPowerKernelAmbient_injective I 0 V.unop
    have h : V.unop ≤ U.unop := leOfHom f.unop
    rw [Subsingleton.elim f (homOfLE h).op, idealPowerKernelAmbient_restrict,
      idealPowerKernelOneAt_ambient, idealPowerKernelOneAt_ambient]
    exact (X.presheaf.map (homOfLE h).op).hom.map_one)

private theorem reesUnit_eval {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    (reesUnit I).eval (op U) = idealPowerKernelOneAt I U := rfl

private theorem reesPiece_negative_section_eq_zero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : n < 0) (U : X.Opens) (x : (reesPiece I n).val.obj (op U)) : x = 0 := by
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  exact (ModuleCat.subsingleton_of_isZero
    (E.map_isZero (reesPiece_negative_isZero I n hn))).elim _ _

/-- The product of a local section of `Iⁿ` and a local section of `Iᵐ`, as a local section
of `Iⁿ⁺ᵐ`. -/
public def idealPowerKernelMulResult {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ)
    (U : X.Opens) (x : (idealPowerKernel I n).val.obj (op U))
    (y : (idealPowerKernel I m).val.obj (op U)) :
    (idealPowerKernel I (n + m)).val.obj (op U) :=
  (idealPowerKernelSubmoduleEquiv I (n + m) U).symm
    ⟨idealPowerKernelAmbient I n U x * idealPowerKernelAmbient I m U y,
      idealPowerKernel_product_quotient_eq_zero I n m U x y⟩

private theorem idealPowerKernelMulResult_ambient {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) (U : X.Opens) (x : (idealPowerKernel I n).val.obj (op U))
    (y : (idealPowerKernel I m).val.obj (op U)) :
    idealPowerKernelAmbient I (n + m) U (idealPowerKernelMulResult I n m U x y) =
      idealPowerKernelAmbient I n U x * idealPowerKernelAmbient I m U y := by
  rw [← idealPowerKernelSubmoduleEquiv_coe]
  exact congrArg Subtype.val
    ((idealPowerKernelSubmoduleEquiv I (n + m) U).apply_symm_apply _)

/-- The product of two sections is the section whose ambient image is the product of the images. -/
private theorem idealPowerKernelMulResult_eq {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ)
    (U : X.Opens) (x : (idealPowerKernel I n).val.obj (op U))
    (y : (idealPowerKernel I m).val.obj (op U)) (z : (idealPowerKernel I (n + m)).val.obj (op U))
    (h : idealPowerKernelAmbient I (n + m) U z =
      idealPowerKernelAmbient I n U x * idealPowerKernelAmbient I m U y) :
    idealPowerKernelMulResult I n m U x y = z :=
  idealPowerKernelAmbient_injective I (n + m) U
    ((idealPowerKernelMulResult_ambient I n m U x y).trans h.symm)

private theorem idealPowerKernelMulResult_restrict {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) (U V : X.Opens) (h : U ≤ V) (x : (idealPowerKernel I n).val.obj (op V))
    (y : (idealPowerKernel I m).val.obj (op V)) :
    ConcreteCategory.hom ((idealPowerKernel (I := I) (n + m)).val.map (homOfLE h).op)
        (idealPowerKernelMulResult I n m V x y) =
      idealPowerKernelMulResult I n m U
        (ConcreteCategory.hom ((idealPowerKernel I n).val.map (homOfLE h).op) x)
        (ConcreteCategory.hom ((idealPowerKernel I m).val.map (homOfLE h).op) y) := by
  refine (idealPowerKernelMulResult_eq I n m U _ _ _ ?_).symm
  rw [idealPowerKernelAmbient_restrict, idealPowerKernelMulResult_ambient, map_mul,
    ← idealPowerKernelAmbient_restrict, ← idealPowerKernelAmbient_restrict]

/-- Multiplication `Iⁿ(U) × Iᵐ(U) → Iⁿ⁺ᵐ(U)`, as a biadditive map. -/
public def idealPowerKernelMulApp {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ)
    (U : X.Opens) :
    (idealPowerKernel I n).val.obj (op U) →+
      (idealPowerKernel I m).val.obj (op U) →+
        (idealPowerKernel I (n + m)).val.obj (op U) where
  toFun x := {
    toFun := idealPowerKernelMulResult I n m U x
    map_zero' := by
      apply idealPowerKernelAmbient_injective
      change idealPowerKernelAmbient I (n + m) U (idealPowerKernelMulResult I n m U x 0) =
        idealPowerKernelAmbient I (n + m) U 0
      rw [idealPowerKernelMulResult_ambient, idealPowerKernelAmbient_zero,
        idealPowerKernelAmbient_zero, mul_zero]
    map_add' := by
      intro y z
      apply idealPowerKernelAmbient_injective
      change idealPowerKernelAmbient I (n + m) U
          (idealPowerKernelMulResult I n m U x (y + z)) =
        idealPowerKernelAmbient I (n + m) U
          (idealPowerKernelMulResult I n m U x y + idealPowerKernelMulResult I n m U x z)
      simp only [idealPowerKernelAmbient_add, idealPowerKernelMulResult_ambient]
      ring }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    apply idealPowerKernelAmbient_injective
    change idealPowerKernelAmbient I (n + m) U (idealPowerKernelMulResult I n m U 0 y) =
      idealPowerKernelAmbient I (n + m) U 0
    rw [idealPowerKernelMulResult_ambient, idealPowerKernelAmbient_zero,
      idealPowerKernelAmbient_zero, zero_mul]
  map_add' := by
    intro x x'
    apply AddMonoidHom.ext
    intro y
    apply idealPowerKernelAmbient_injective
    change idealPowerKernelAmbient I (n + m) U (idealPowerKernelMulResult I n m U (x + x') y) =
      idealPowerKernelAmbient I (n + m) U
        (idealPowerKernelMulResult I n m U x y + idealPowerKernelMulResult I n m U x' y)
    simp only [idealPowerKernelAmbient_add, idealPowerKernelMulResult_ambient]
    ring

/-- Multiplication of local sections of powers of `I` is linear in the first variable. -/
public theorem idealPowerKernelMulApp_smul_left {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U))
    (x : (idealPowerKernel I n).val.obj (op U)) (y : (idealPowerKernel I m).val.obj (op U)) :
    idealPowerKernelMulApp I n m U (r • x) y = r • idealPowerKernelMulApp I n m U x y :=
  idealPowerKernelMulResult_eq I n m U _ y (r • idealPowerKernelMulResult I n m U x y) (by
    simp only [idealPowerKernelMulResult_ambient, idealPowerKernelAmbient_smul]
    ring)

/-- Multiplication of local sections of powers of `I` is linear in the second variable. -/
public theorem idealPowerKernelMulApp_smul_right {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U))
    (x : (idealPowerKernel I n).val.obj (op U)) (y : (idealPowerKernel I m).val.obj (op U)) :
    idealPowerKernelMulApp I n m U x (r • y) = r • idealPowerKernelMulApp I n m U x y :=
  idealPowerKernelMulResult_eq I n m U x _ (r • idealPowerKernelMulResult I n m U x y) (by
    simp only [idealPowerKernelMulResult_ambient, idealPowerKernelAmbient_smul]
    ring)

/-- Multiplication of local sections of powers of `I` commutes with restriction. -/
public theorem idealPowerKernelMulApp_naturality {X : Scheme.{u}} (I : X.IdealSheafData)
    (n m : ℕ) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : (idealPowerKernel I n).val.obj U)
    (y : (idealPowerKernel I m).val.obj U) :
    (idealPowerKernel I (n + m)).val.map f (idealPowerKernelMulApp I n m U.unop x y) =
      idealPowerKernelMulApp I n m V.unop ((idealPowerKernel I n).val.map f x)
        ((idealPowerKernel I m).val.map f y) := by
  have h : V.unop ≤ U.unop := leOfHom f.unop
  rw [Subsingleton.elim f (homOfLE h).op]
  exact idealPowerKernelMulResult_restrict I n m V.unop U.unop h x y

/-- The zero bilinear map between sheaves of modules. -/
public def zeroSheafBilinearMap {X : Scheme.{u}}
    (M N P : SheafOfModules.{u} X.ringCatSheaf) : SheafOfModules.BilinearMap M N P where
  app _ := 0
  map_smul_left _ _ _ _ := by simp
  map_smul_right _ _ _ _ := by simp
  naturality f _ _ := by
    change ConcreteCategory.hom (P.val.map f) 0 = 0
    exact map_zero _

/-- Multiplication on the Rees algebra: on nonnegative degrees it is multiplication of sections
of `𝒪_X`, and it is zero as soon as one of the degrees is negative. -/
public def reesMultiplication {X : Scheme.{u}} (I : X.IdealSheafData) (i j : ℤ) :
    SheafOfModules.BilinearMap (reesPiece I i) (reesPiece I j) (reesPiece I (i + j)) := by
  cases i with
  | ofNat n =>
    cases j with
    | ofNat m =>
      exact {
        app U := idealPowerKernelMulApp I n m U.unop
        map_smul_left U r x y := idealPowerKernelMulApp_smul_left I n m U.unop r x y
        map_smul_right U r x y := idealPowerKernelMulApp_smul_right I n m U.unop r x y
        naturality f x y := idealPowerKernelMulApp_naturality I n m f x y }
    | negSucc m => exact zeroSheafBilinearMap _ _ _
  | negSucc n => exact zeroSheafBilinearMap _ _ _

/-- The image in `Γ(X, U)` of a section of the degree-`n` piece of the Rees algebra, taken to
be `0` in negative degrees. -/
public def reesPieceAmbient {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ) (U : X.Opens)
    (x : (reesPiece I n).val.obj (op U)) : Γ(X, U) :=
  match n with
  | .ofNat k => idealPowerKernelAmbient I k U x
  | .negSucc _ => 0

/-- The image in `Γ(X, U)` of the zero homogeneous section is zero. -/
public theorem reesPieceAmbient_zero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (U : X.Opens) : reesPieceAmbient I n U 0 = 0 := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_zero I k U
  | negSucc k => rfl

/-- The image in `Γ(X, U)` of the unit of the Rees algebra is `1`. -/
public theorem reesUnit_ambient {X : Scheme.{u}} (I : X.IdealSheafData) (U : (Opens X)ᵒᵖ) :
    reesPieceAmbient I 0 U.unop ((reesUnit I).eval U) = 1 := by
  change idealPowerKernelAmbient I 0 U.unop ((reesUnit I).eval U) = 1
  rw [reesUnit_eval]
  exact idealPowerKernelOneAt_ambient I U.unop

/-- In nonnegative degrees a homogeneous section is determined by its image in `Γ(X, U)`. -/
public theorem reesPieceAmbient_injective {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : 0 ≤ n) (U : X.Opens) : Function.Injective (reesPieceAmbient I n U) := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_injective I k U
  | negSucc k => omega

/-- Transporting a homogeneous section along an equality of degrees does not change its image
in `Γ(X, U)`. -/
public theorem reesPieceAmbient_cast {X : Scheme.{u}} (I : X.IdealSheafData) {n m : ℤ}
    (h : n = m) (U : X.Opens) (x : (reesPiece I n).val.obj (op U)) :
    reesPieceAmbient I m U
      (cast (congrArg (fun d => ↥((reesPiece I d).val.obj (op U))) h) x) =
        reesPieceAmbient I n U x := by
  cases h
  rfl

/-- The image in `Γ(X, U)` of a sum of homogeneous sections is the sum of their images. -/
public theorem reesPieceAmbient_add {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (U : X.Opens) (x y : (reesPiece I n).val.obj (op U)) :
    reesPieceAmbient I n U (x + y) =
      reesPieceAmbient I n U x + reesPieceAmbient I n U y := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_add I k U x y
  | negSucc k => exact (add_zero (0 : Γ(X, U))).symm

/-- The image in `Γ(X, U)` of a scalar multiple of a homogeneous section is the corresponding
product in `Γ(X, U)`. -/
public theorem reesPieceAmbient_smul {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U))
    (x : (reesPiece I n).val.obj (op U)) :
    reesPieceAmbient I n U (r • x) =
      ringSectionToGamma r * reesPieceAmbient I n U x := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_smul I k U r x
  | negSucc k => exact (mul_zero (ringSectionToGamma r)).symm

/-- Taking the image in `Γ(X, U)` of a homogeneous section commutes with restriction. -/
public theorem reesPieceAmbient_restrict {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (U V : X.Opens) (h : U ≤ V) (x : (reesPiece I n).val.obj (op V)) :
    reesPieceAmbient I n U
        (ConcreteCategory.hom ((reesPiece I n).val.map (homOfLE h).op) x) =
      X.presheaf.map (homOfLE h).op (reesPieceAmbient I n V x) := by
  cases n with
  | ofNat k => exact idealPowerKernelAmbient_restrict I k U V h x
  | negSucc k =>
      exact (map_zero (ConcreteCategory.hom (X.presheaf.map (homOfLE h).op))).symm

/-- The image in `Γ(X, U)` of a product of homogeneous sections is the product of their
images. -/
public theorem reesMultiplication_ambient {X : Scheme.{u}} (I : X.IdealSheafData) (i j : ℤ)
    (U : X.Opens) (x : (reesPiece I i).val.obj (op U)) (y : (reesPiece I j).val.obj (op U)) :
    reesPieceAmbient I (i + j) U ((reesMultiplication I i j).app (op U) x y) =
        reesPieceAmbient I i U x * reesPieceAmbient I j U y := by
  cases i with
  | ofNat n =>
    cases j with
    | ofNat m =>
      change idealPowerKernelAmbient I (n + m) U (idealPowerKernelMulResult I n m U x y) = _
      exact idealPowerKernelMulResult_ambient I n m U x y
    | negSucc m => exact (reesPieceAmbient_zero I _ U).trans (by simp [reesPieceAmbient])
  | negSucc n => exact (reesPieceAmbient_zero I _ U).trans (by cases j <;> simp [reesPieceAmbient])

/-- Over an affine open `U`, the degree-`n` sections of the Rees algebra are `I(U)ⁿ`. -/
public def reesPieceAffineEquiv {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ) (hn : 0 ≤ n)
    (U : X.affineOpens) :
    (reesPiece I n).val.obj (op U.1) ≃+ ↥(I.ideal U ^ n.toNat) := by
  cases n with
  | ofNat k =>
    change (idealPowerKernel I k).val.obj (op U.1) ≃+ ↥(I.ideal U ^ k)
    exact idealPowerKernelSectionsEquiv I k U
  | negSucc k => omega

/-- The affine-local description of the Rees algebra is given by the image in `Γ(X, U)`. -/
public theorem reesPieceAffineEquiv_coe {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : 0 ≤ n) (U : X.affineOpens) (x : (reesPiece I n).val.obj (op U.1)) :
    (reesPieceAffineEquiv I n hn U x : Γ(X, U.1)) = reesPieceAmbient I n U.1 x := by
  cases n with
  | ofNat k =>
    change (idealPowerKernelSectionsEquiv I k U x : Γ(X, U.1)) =
      idealPowerKernelAmbient I k U.1 x
    exact idealPowerKernelSectionsEquiv_coe I k U x
  | negSucc k => omega

private theorem freeEmpty_isQuasicoherent {X : Scheme.{u}} :
    (SheafOfModules.free (R := X.ringCatSheaf) PEmpty).IsQuasicoherent := inferInstance

/-- Over an affine open, the image in `Γ(X, U)` of a section of the degree-`n` piece of the Rees
algebra lies in the `n`-th power of the ideal. -/
public theorem reesPieceAmbient_mem_affine {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : 0 ≤ n) (U : X.affineOpens) (x : (reesPiece I n).val.obj (op U.1)) :
    reesPieceAmbient I n U.1 x ∈ I.ideal U ^ n.toNat :=
  (reesPieceAffineEquiv_coe I n hn U x) ▸ (reesPieceAffineEquiv I n hn U x).property

/-- Every homogeneous piece of the Rees algebra is quasi-coherent. -/
public theorem reesPiece_isQuasicoherent {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ) :
    (reesPiece I n).IsQuasicoherent := by
  cases n with
  | ofNat k => exact idealPowerKernel_isQuasicoherent I k
  | negSucc k => exact freeEmpty_isQuasicoherent

/-- The affine-local description of the Rees algebra is linear over the sections of `𝒪_X`. -/
public theorem reesPieceAffineEquiv_smul {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : 0 ≤ n) (U : X.affineOpens) (r : X.ringCatSheaf.obj.obj (op U.1))
    (a : (reesPiece I n).val.obj (op U.1)) :
    (reesPieceAffineEquiv I n hn U (r • a) : X.presheaf.obj (op U.1)) =
      (show X.presheaf.obj (op U.1) from r) *
        (reesPieceAffineEquiv I n hn U a : X.presheaf.obj (op U.1)) := by
  rw [reesPieceAffineEquiv_coe, reesPieceAffineEquiv_coe]
  exact reesPieceAmbient_smul I n U.1 r a

/-- The affine-local description of the Rees algebra turns homogeneous multiplication into
multiplication of sections of `𝒪_X`. -/
public theorem reesPieceAffineEquiv_mul {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℤ)
    (hn : 0 ≤ n) (hm : 0 ≤ m) (U : X.affineOpens) (a : (reesPiece I n).val.obj (op U.1))
    (b : (reesPiece I m).val.obj (op U.1)) :
    (reesPieceAffineEquiv I (n + m) (add_nonneg hn hm) U
      ((reesMultiplication I n m).app (op U.1) a b) : X.presheaf.obj (op U.1)) =
      (reesPieceAffineEquiv I n hn U a : X.presheaf.obj (op U.1)) *
        (reesPieceAffineEquiv I m hm U b : X.presheaf.obj (op U.1)) := by
  rw [reesPieceAffineEquiv_coe, reesPieceAffineEquiv_coe, reesPieceAffineEquiv_coe]
  exact reesMultiplication_ambient I n m U.1 a b

/-- The affine-local description of the Rees algebra sends its unit to `1`. -/
public theorem reesPieceAffineEquiv_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (reesPieceAffineEquiv I 0 (le_refl 0) U ((reesUnit I).eval (op U.1)) :
      X.presheaf.obj (op U.1)) = 1 :=
  (reesPieceAffineEquiv_coe I 0 (le_refl 0) U _).trans (reesUnit_ambient I (op U.1))

/-- The affine-local descriptions of the Rees algebra are compatible with restriction. -/
public theorem reesPieceAffineEquiv_restrict {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)
    (hn : 0 ≤ n) (U V : X.affineOpens) (h : U.1 ≤ V.1)
    (a : (reesPiece I n).val.obj (op V.1)) :
    (reesPieceAffineEquiv I n hn U
      ((reesPiece I n).val.map (homOfLE h).op a) : X.presheaf.obj (op U.1)) =
      X.presheaf.map (homOfLE h).op
        (reesPieceAffineEquiv I n hn V a : X.presheaf.obj (op V.1)) :=
  (reesPieceAffineEquiv_coe I n hn U _).trans ((reesPieceAmbient_restrict I n U.1 V.1 h a).trans
    (congrArg (fun z => ConcreteCategory.hom (X.presheaf.map (homOfLE h).op) z)
      (reesPieceAffineEquiv_coe I n hn V a).symm))

private theorem reesPiece_heq_of_ambient {X : Scheme.{u}} (I : X.IdealSheafData) {i j : ℤ}
    (h : i = j) (U : (Opens X)ᵒᵖ) (x : (reesPiece I i).val.obj U)
    (y : (reesPiece I j).val.obj U)
    (hxy : 0 ≤ j → reesPieceAmbient I i U.unop x = reesPieceAmbient I j U.unop y) :
    HEq x y := by
  cases h
  by_cases hi : i < 0
  · exact heq_of_eq ((reesPiece_negative_section_eq_zero I i hi U.unop x).trans
      (reesPiece_negative_section_eq_zero I i hi U.unop y).symm)
  · exact heq_of_eq (reesPieceAmbient_injective I i (by omega) U.unop (hxy (by omega)))

/-- Multiplication on the Rees algebra is commutative. -/
public theorem reesMultiplication_comm {X : Scheme.{u}} (I : X.IdealSheafData) (i j : ℤ)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) (b : (reesPiece I j).val.obj U) :
    HEq ((reesMultiplication I i j).app U a b) ((reesMultiplication I j i).app U b a) :=
  reesPiece_heq_of_ambient I (add_comm i j) U _ _ fun _ =>
    (reesMultiplication_ambient I i j U.unop a b).trans
      ((mul_comm _ _).trans (reesMultiplication_ambient I j i U.unop b a).symm)

/-- Multiplication on the Rees algebra is associative. -/
public theorem reesMultiplication_assoc {X : Scheme.{u}} (I : X.IdealSheafData) (i j k : ℤ)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) (b : (reesPiece I j).val.obj U)
    (c : (reesPiece I k).val.obj U) :
    HEq ((reesMultiplication I (i + j) k).app U ((reesMultiplication I i j).app U a b) c)
        ((reesMultiplication I i (j + k)).app U a ((reesMultiplication I j k).app U b c)) :=
  reesPiece_heq_of_ambient I (add_assoc i j k) U _ _ fun _ => by
    calc
      reesPieceAmbient I ((i + j) + k) U.unop
            ((reesMultiplication I (i + j) k).app U ((reesMultiplication I i j).app U a b) c) =
          reesPieceAmbient I (i + j) U.unop ((reesMultiplication I i j).app U a b) *
            reesPieceAmbient I k U.unop c :=
        reesMultiplication_ambient I (i + j) k U.unop _ _
      _ = (reesPieceAmbient I i U.unop a * reesPieceAmbient I j U.unop b) *
            reesPieceAmbient I k U.unop c := by rw [reesMultiplication_ambient I i j]
      _ = reesPieceAmbient I i U.unop a *
            (reesPieceAmbient I j U.unop b * reesPieceAmbient I k U.unop c) := mul_assoc _ _ _
      _ = reesPieceAmbient I i U.unop a *
            reesPieceAmbient I (j + k) U.unop ((reesMultiplication I j k).app U b c) := by
          rw [reesMultiplication_ambient I j k]
      _ = _ := (reesMultiplication_ambient I i (j + k) U.unop _ _).symm

/-- The unit of the Rees algebra is a left identity. -/
public theorem reesMultiplication_one_left {X : Scheme.{u}} (I : X.IdealSheafData) (i : ℤ)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) :
    HEq ((reesMultiplication I 0 i).app U ((reesUnit I).eval U) a) a :=
  reesPiece_heq_of_ambient I (zero_add i) U _ _ fun _ =>
    (reesMultiplication_ambient I 0 i U.unop _ _).trans (by rw [reesUnit_ambient, one_mul])

/-- The unit of the Rees algebra is a right identity. -/
public theorem reesMultiplication_one_right {X : Scheme.{u}} (I : X.IdealSheafData) (i : ℤ)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) :
    HEq ((reesMultiplication I i 0).app U a ((reesUnit I).eval U)) a :=
  reesPiece_heq_of_ambient I (add_zero i) U _ _ fun _ =>
    (reesMultiplication_ambient I i 0 U.unop _ _).trans (by rw [reesUnit_ambient, mul_one])

/-- The Rees algebra `⨁_{n ≥ 0} Iⁿ` of a quasi-coherent ideal sheaf, as a sheaf of `ℤ`-graded
algebras over the structure sheaf of `X`. -/
public def reesGradedAlgebra {X : Scheme.{u}} (I : X.IdealSheafData) :
    SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece := reesPiece I
  mul := reesMultiplication I
  one := reesUnit I
  mul_assoc := reesMultiplication_assoc I
  one_mul := reesMultiplication_one_left I
  mul_one := reesMultiplication_one_right I

/-- A Rees algebra sheaf for an ideal sheaf, specified by its homogeneous sections on
affine opens. The compatibility fields make these identifications canonical. -/
public structure ReesAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) where
  /-- The underlying sheaf of graded algebras. -/
  algebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf
  /-- Homogeneous multiplication is commutative. -/
  mul_comm (i j : ℤ) (U : (Opens X)ᵒᵖ)
      (a : (algebra.piece i).val.obj U) (b : (algebra.piece j).val.obj U) :
    HEq ((algebra.mul i j).app U a b) ((algebra.mul j i).app U b a)
  /-- Negative homogeneous pieces vanish. -/
  negative_isZero (n : ℤ) (hn : n < 0) : IsZero (algebra.piece n)
  /-- Every homogeneous piece is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent
  /-- Over an affine open `U`, the degree-`n` sections are the `n`-th power of `I(U)`. -/
  pieceEquiv (n : ℤ) (hn : 0 ≤ n) (U : X.affineOpens) :
    (algebra.piece n).val.obj (op U.1) ≃+ ↥(I.ideal U ^ n.toNat)
  /-- The affine-local identification is linear over the sections of `𝒪_X`. -/
  pieceEquiv_smul (n : ℤ) (hn : 0 ≤ n) (U : X.affineOpens)
      (r : X.ringCatSheaf.obj.obj (op U.1)) (a : (algebra.piece n).val.obj (op U.1)) :
    ((pieceEquiv n hn U (r • a)) : X.presheaf.obj (op U.1)) =
      (show X.presheaf.obj (op U.1) from r) *
        (pieceEquiv n hn U a : X.presheaf.obj (op U.1))
  /-- The affine-local identification turns homogeneous multiplication into multiplication
  of sections of `𝒪_X`. -/
  pieceEquiv_mul (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
      (U : X.affineOpens) (a : (algebra.piece n).val.obj (op U.1))
      (b : (algebra.piece m).val.obj (op U.1)) :
    ((pieceEquiv (n + m) (add_nonneg hn hm) U ((algebra.mul n m).app (op U.1) a b)) :
      X.presheaf.obj (op U.1)) =
        (pieceEquiv n hn U a : X.presheaf.obj (op U.1)) *
          (pieceEquiv m hm U b : X.presheaf.obj (op U.1))
  /-- The affine-local identification sends the unit to `1`. -/
  pieceEquiv_one (U : X.affineOpens) :
    ((pieceEquiv 0 (le_refl 0) U (algebra.one.eval (op U.1))) :
      X.presheaf.obj (op U.1)) = 1
  /-- The affine-local identifications are compatible with restriction. -/
  pieceEquiv_restrict (n : ℤ) (hn : 0 ≤ n) (U V : X.affineOpens)
      (h : U.1 ≤ V.1) (a : (algebra.piece n).val.obj (op V.1)) :
    ((pieceEquiv n hn U ((algebra.piece n).val.map (homOfLE h).op a)) :
      X.presheaf.obj (op U.1)) =
        X.presheaf.map (homOfLE h).op
          ((pieceEquiv n hn V a : X.presheaf.obj (op V.1)))

/-- The Rees algebra sheaf `⨁ₙ Iⁿ`, together with its affine-local characterization. -/
public def reesAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) : ReesAlgebraData I where
  algebra := reesGradedAlgebra I
  mul_comm := reesMultiplication_comm I
  negative_isZero := reesPiece_negative_isZero I
  isQuasicoherent := reesPiece_isQuasicoherent I
  pieceEquiv := reesPieceAffineEquiv I
  pieceEquiv_smul := reesPieceAffineEquiv_smul I
  pieceEquiv_mul := reesPieceAffineEquiv_mul I
  pieceEquiv_one := reesPieceAffineEquiv_one I
  pieceEquiv_restrict := reesPieceAffineEquiv_restrict I

/-- **Stacks Project, Tag 01OG.** A graded sheaf with the canonical affine-local description
of `⨁ₙ Iⁿ` exists. -/
@[stacks 01OG "Rees algebra sheaf"]
public theorem exists_reesAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) :
    Nonempty (ReesAlgebraData I) :=
  ⟨reesAlgebraData I⟩

/-- The quasi-coherent graded Rees algebra as a relative `Proj` situation. -/
public def reesSituation {X : Scheme.{u}} (I : X.IdealSheafData) :
    Stacks.RelativeProj.Situation.{u} where
  base := X
  algebra := (reesAlgebraData I).algebra
  mul_comm := (reesAlgebraData I).mul_comm
  negative_isZero := (reesAlgebraData I).negative_isZero
  isQuasicoherent := (reesAlgebraData I).isQuasicoherent

end Stacks.Blowup

end
