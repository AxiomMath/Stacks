module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionTransport
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.DifferentialGradedAlgebra

/-!
# The differential of a Koszul chain complex is the Koszul differential of its functional

Let `O♯` be a sheaf of commutative rings on a site, let `F` be a sheaf of `O♯`-modules, let `A`
be a bundle of tensor, exterior and symmetric algebras of `F` and let `φ : F ⟶ O♯`. The Koszul
complex of `φ` is taken as data in `Stacks.RegularSequence.KoszulChainData`, which imposes only
the graded Leibniz rule and the value on a degree-one generator; it does not say that its
degree-lowering morphisms are the Koszul differential of `φ`, because the Koszul differential is
constructed on the *realized* exterior algebra `SheafOfModules.sheafifiedExteriorAlgebra J F` and
not on the exterior powers of an abstract bundle.

This file closes that gap. The uniqueness half of Stacks tag 062K,
`SheafOfModules.koszulD_unique`, says a graded derivation of the realized exterior algebra whose
value on a degree-one local section `e` is `φ(e)` *is* the Koszul differential. Transporting the
chain data's differential onto the realized algebra along the canonical degreewise comparison of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.sheafifiedPieceIso` turns it into such a
derivation, and transporting the conclusion back identifies it with the Koszul differential of
the functional attached to `φ`.

The consequence the Koszul complex needs is that contraction by a coordinate functional is a
**cocycle**: for a finite free `F` the contraction `δⱼ` anticommutes with the differential of the
complex itself,

`δⱼ d + d δⱼ = 0`,

so `δⱼ` is a degree-one chain map of the complex into itself. Anticommutation of `δⱼ` with the
Koszul differential of an arbitrary functional is already available
(`Stacks.RegularSequence.KoszulChainData.koszulD_comp_coordKoszulD_comm`); what was missing, and is
supplied here, is that the complex's own differential is such a Koszul differential.

## Main definitions

* `Stacks.SheafOfModules.unitExteriorFunctional`: **the functional on `F` attached to a morphism
  `φ : F ⟶ O♯`**, that is, `φ` read as a linear form on the sections over each object.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.sheafifiedExteriorPieceIso`: the canonical
  degreewise comparison of the realized exterior algebra `⋀(F)` with the exterior powers of a
  bundle of algebras of `F`.
* `Stacks.RegularSequence.KoszulChainData.dOf`: the chain data's differential at independently
  named degrees, `⋀ᵖ F ⟶ ⋀^q F` for `q + 1 = p`.
* `Stacks.RegularSequence.KoszulChainData.sheafifiedD`: that differential transported onto the
  homogeneous pieces of the realized exterior algebra.

## Main results

* `Stacks.RegularSequence.KoszulChainData.isKoszulDerivation_sheafifiedD`: **the transported
  differential is a graded derivation of `⋀(F)`** — the graded Leibniz rule of the chain data,
  carried across the comparison, which is multiplicative on homogeneous local sections.
* `Stacks.RegularSequence.KoszulChainData.dOf_eq_koszulD`: **the chain data's differential is the
  Koszul differential of the functional attached to `φ`.** This is the uniqueness half of Stacks
  tag 062K made available for an abstract bundle of algebras.
* `Stacks.RegularSequence.KoszulChainData.chain_d_eq_koszulD`: the same, read on the terms of the
  associated chain complex, where it identifies `chain.d` itself.
* `Stacks.RegularSequence.KoszulChainData.coordKoszulD_comp_chain_d_comm` and
  `chain_d_comp_coordKoszulD_comm`: **the coordinate contraction `δⱼ` anticommutes with the
  differential of the Koszul complex**, in either order, on the terms of the complex. These are
  the cocycle identities.
* `Stacks.RegularSequence.KoszulChainData.coordKoszulD_comp_dOf_comm` and
  `dOf_comp_coordKoszulD_comm`: the same two identities on the exterior powers.

## Implementation notes

**Why the differential is transported rather than the uniqueness theorem reproved.** The
induction behind uniqueness — a sectionwise exterior form is built from scalars, sums and left
multiplication by a degree-one generator — is carried out once, on the realized exterior algebra,
in `SheafOfModules.koszulD_eq_on_exteriorUnit`, where the homogeneous pieces are sheafifications
and two morphisms out of a sheafification agreeing on unit images are equal. An abstract bundle
has no such presentation of its pieces, so the induction cannot be run there; the comparison
isomorphism is the only route, and it suffices, because the two hypotheses of uniqueness are
preserved by it. The Leibniz rule is preserved because the comparison is multiplicative
(`sheafifiedPieceIso_mul`), and the value on a generator because it matches the two degree-one
generators (`sheafifiedPieceIso_generator`) and the two units (`sheafifiedPieceIso_one`).

**Degree bookkeeping.** The chain data indexes its differential as `⋀ⁿ F ⟶ ⋀^{n-1} F`, whereas a
graded derivation is indexed by two degrees with `q + 1 = p`; `dOf` is the second form, and the
transport between them is the identity once `q` is substituted for `p - 1`. The Leibniz rule of
the chain data is stated with `Stacks.degCast` and that of a graded derivation with
`SheafOfModules.gradedCast`; both are transport along an equality of integer degrees, and
`Stacks.gradedCast_eq_degCast` identifies them.

**Term-mode rewriting.** Several steps apply `map_add`, `map_smul` or `map_zsmul` to a morphism of
sheaves of modules read on sections. The carrier of a homogeneous piece and the carrier of the
module of sections over an object are the same type with instances that are not syntactically
equal, so a rewrite whose motive mixes them is refused as not type-correct at `implicit`
transparency; `Eq.trans` and `congrArg` are checked at full transparency and are used instead.
This is the obstruction recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulChainDataAlgebras`.

**The functional attached to `φ`.** `Stacks.SheafOfModules.unitExteriorFunctional` is built from
`Stacks.RegularSequence.unitScalar`, a definition with an ascribed result type rather than a type
ascription: the sections of `SheafOfModules.unit R` are the ring of sections only after unfolding
`unit`, and instance search does not unfold it, so the scalar has to be retyped for the module
structure. Its naturality is the naturality of `φ`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w

namespace Stacks

/-- Transport along an equality of integer degrees, in the two spellings the graded Leibniz rules
of this development use. -/
theorem gradedCast_eq_degCast {T : ℤ → Type w} {i j : ℤ} (h : i = j) (x : T i) :
    SheafOfModules.gradedCast T h x = Stacks.degCast (F := T) h x := by
  subst h; rfl

end Stacks

namespace Stacks.SheafOfModules

/-! ### The functional attached to a morphism into the structure sheaf -/

section UnitFunctional

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  {F : _root_.SheafOfModules.{w} (toRingCat J Osharp)}

/-- **The functional on `F` attached to a morphism `φ : F ⟶ O♯`**: over each object it is `φ` read
as a linear form on the sections, and it is compatible with restriction because `φ` is a morphism
of sheaves of modules. -/
def unitExteriorFunctional (φ : F ⟶ _root_.SheafOfModules.unit (toRingCat J Osharp)) :
    PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val where
  dual U :=
    { toFun := Stacks.RegularSequence.unitScalar φ U
      map_add' := fun x y => (φ.val.app U).hom.map_add x y
      map_smul' := fun r x => (φ.val.app U).hom.map_smul r x }
  naturality _ m := (PresheafOfModules.naturality_apply φ.val _ m).symm

/-- The functional attached to `φ` reads off the scalar `φ` assigns to a local section. -/
theorem unitExteriorFunctional_dual_apply
    (φ : F ⟶ _root_.SheafOfModules.unit (toRingCat J Osharp)) (U : Cᵒᵖ) (e : F.val.obj U) :
    (unitExteriorFunctional φ).dual U e = Stacks.RegularSequence.unitScalar φ U e :=
  rfl

end UnitFunctional

end Stacks.SheafOfModules

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The comparison of the realized exterior algebra with a bundle's -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- **The canonical degreewise comparison** of the realized exterior algebra `⋀(F)` with the
exterior powers of a bundle of algebras of `F`. The bundle's exterior algebra has the universal
property by its field `exterior_isExteriorAlgebra`, so this is the comparison that property
produces. -/
def sheafifiedExteriorPieceIso (n : ℤ) :
    (sheafifiedExteriorAlgebra J F).piece n ≅ A.exterior.piece n :=
  A.exterior_isExteriorAlgebra.sheafifiedPieceIso n

/-- The comparison carries the degree-one generator of `⋀(F)` to the bundle's. -/
theorem sheafifiedExteriorPieceIso_generator :
    sheafifiedExteriorGenerator J F ≫ (A.sheafifiedExteriorPieceIso 1).hom =
      A.exteriorGenerator :=
  A.exterior_isExteriorAlgebra.sheafifiedPieceIso_generator

/-- The comparison is multiplicative on homogeneous local sections. -/
theorem sheafifiedExteriorPieceIso_mul (i j : ℤ) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece i).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece j).val.obj U) :
    ((A.sheafifiedExteriorPieceIso (i + j)).hom).val.app U
        (((sheafifiedExteriorAlgebra J F).mul i j).app U x y) =
      (A.exterior.mul i j).app U (((A.sheafifiedExteriorPieceIso i).hom).val.app U x)
        (((A.sheafifiedExteriorPieceIso j).hom).val.app U y) :=
  A.exterior_isExteriorAlgebra.sheafifiedPieceIso_mul i j U x y

/-- The comparison carries the unit of `⋀(F)` to the bundle's unit. -/
theorem sheafifiedExteriorPieceIso_one (U : Cᵒᵖ) :
    ((A.sheafifiedExteriorPieceIso 0).hom).val.app U
        ((sheafifiedExteriorAlgebra J F).one.eval U) = A.exterior.one.eval U :=
  A.exterior_isExteriorAlgebra.sheafifiedPieceIso_one U

/-- The comparison carries the bundle's unit back to the unit of `⋀(F)`. -/
theorem sheafifiedExteriorPieceIso_inv_one (U : Cᵒᵖ) :
    ((A.sheafifiedExteriorPieceIso 0).inv).val.app U (A.exterior.one.eval U) =
      (sheafifiedExteriorAlgebra J F).one.eval U :=
  Eq.trans
    (congrArg ((A.sheafifiedExteriorPieceIso 0).inv.val.app U)
      (A.sheafifiedExteriorPieceIso_one U).symm)
    (SheafOfModules.iso_inv_hom_app_apply (A.sheafifiedExteriorPieceIso 0) U _)

/-- The comparison is injective on local sections, being an isomorphism. -/
theorem sheafifiedExteriorPieceIso_hom_app_injective (n : ℤ) (U : Cᵒᵖ)
    {a b : ((sheafifiedExteriorAlgebra J F).piece n).val.obj U}
    (hab : (A.sheafifiedExteriorPieceIso n).hom.val.app U a =
      (A.sheafifiedExteriorPieceIso n).hom.val.app U b) : a = b :=
  Eq.trans (SheafOfModules.iso_inv_hom_app_apply (A.sheafifiedExteriorPieceIso n) U a).symm
    (Eq.trans (congrArg ((A.sheafifiedExteriorPieceIso n).inv.val.app U) hab)
      (SheafOfModules.iso_inv_hom_app_apply (A.sheafifiedExteriorPieceIso n) U b))

end Comparison

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace Stacks.RegularSequence.KoszulChainData

/-! ### The chain data's differential, transported onto the realized exterior algebra -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J F}
  {φ : F ⟶ SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A φ)

/-- **The chain data's differential at independently named degrees**, from the exterior power of
degree `p` to the one of degree `q`, for degrees with `q + 1 = p`. This is the indexing a graded
derivation uses; the chain data indexes the same morphism by its source alone. -/
def dOf {p q : ℤ} (h : q + 1 = p) : A.exterior.piece p ⟶ A.exterior.piece q :=
  K.d p ≫ eqToHom (congrArg A.exterior.piece (show p - 1 = q by omega))

/-- At the degrees the chain data itself uses, `dOf` is the chain data's differential. -/
theorem dOf_eq_d {n : ℤ} (h : n - 1 + 1 = n) : K.dOf h = K.d n := by
  simp [dOf]

/-- **The chain data's differential transported onto the realized exterior algebra `⋀(F)`**,
by conjugation with the canonical degreewise comparison. -/
def sheafifiedD {p q : ℤ} (h : q + 1 = p) :
    (SheafOfModules.sheafifiedExteriorAlgebra J F).piece p ⟶
      (SheafOfModules.sheafifiedExteriorAlgebra J F).piece q :=
  (A.sheafifiedExteriorPieceIso p).hom ≫ K.dOf h ≫ (A.sheafifiedExteriorPieceIso q).inv

/-- The comparison intertwines the transported differential with the chain data's. -/
theorem sheafifiedD_comp_hom {p q : ℤ} (h : q + 1 = p) :
    K.sheafifiedD h ≫ (A.sheafifiedExteriorPieceIso q).hom =
      (A.sheafifiedExteriorPieceIso p).hom ≫ K.dOf h := by
  simp [sheafifiedD]

/-- The intertwining identity read on local sections. -/
theorem hom_app_sheafifiedD {p q : ℤ} (h : q + 1 = p) (U : Cᵒᵖ)
    (z : ((SheafOfModules.sheafifiedExteriorAlgebra J F).piece p).val.obj U) :
    (A.sheafifiedExteriorPieceIso q).hom.val.app U ((K.sheafifiedD h).val.app U z) =
      (K.dOf h).val.app U ((A.sheafifiedExteriorPieceIso p).hom.val.app U z) :=
  Eq.trans (SheafOfModules.comp_val_app_apply _ _ U z).symm
    (Eq.trans (SheafOfModules.hom_congr_app_apply (K.sheafifiedD_comp_hom h) U z)
      (SheafOfModules.comp_val_app_apply _ _ U z))

/-- The intertwining identity at the degrees the chain data itself uses, with its differential
`K.d n` in place of `dOf`. -/
private theorem hom_app_sheafifiedD_d {n : ℤ} (h : n - 1 + 1 = n) (U : Cᵒᵖ)
    (z : ((SheafOfModules.sheafifiedExteriorAlgebra J F).piece n).val.obj U) :
    (A.sheafifiedExteriorPieceIso (n - 1)).hom.val.app U ((K.sheafifiedD h).val.app U z) =
      (K.d n).val.app U ((A.sheafifiedExteriorPieceIso n).hom.val.app U z) :=
  Eq.trans (K.hom_app_sheafifiedD h U z)
    (congrArg (fun t => (t.val.app U) ((A.sheafifiedExteriorPieceIso n).hom.val.app U z))
      (K.dOf_eq_d h))

/-- The transported differential read on local sections, in the direction that computes it. -/
theorem sheafifiedD_app {p q : ℤ} (h : q + 1 = p) (U : Cᵒᵖ)
    (z : ((SheafOfModules.sheafifiedExteriorAlgebra J F).piece p).val.obj U) :
    (K.sheafifiedD h).val.app U z =
      (A.sheafifiedExteriorPieceIso q).inv.val.app U
        ((K.dOf h).val.app U ((A.sheafifiedExteriorPieceIso p).hom.val.app U z)) :=
  Eq.trans (SheafOfModules.comp_val_app_apply _ _ U z)
    (SheafOfModules.comp_val_app_apply _ _ U _)

/-- **The transported differential is a graded derivation of `⋀(F)`.** The graded Leibniz rule of
the chain data is carried across the comparison, which is multiplicative on homogeneous local
sections; the two spellings of transport along an equality of degrees are identified by
`Stacks.gradedCast_eq_degCast`. -/
theorem isKoszulDerivation_sheafifiedD :
    SheafOfModules.IsKoszulDerivation J F (fun _ _ h => K.sheafifiedD h) := by
  intro p q p' q' n hp hq hn hA hB U x y
  obtain rfl : p' = p - 1 := by omega
  obtain rfl : q' = q - 1 := by omega
  obtain rfl : n = p + q - 1 := by omega
  refine A.sheafifiedExteriorPieceIso_hom_app_injective (p + q - 1) U ?_
  refine Eq.trans (K.hom_app_sheafifiedD_d hn U _) ?_
  refine Eq.trans (congrArg ((K.d _).val.app U)
    (A.sheafifiedExteriorPieceIso_mul p q U x y)) ?_
  refine Eq.trans (K.d_mul p q U _ _) ?_
  refine Eq.symm (Eq.trans (map_add
    (ConcreteCategory.hom ((A.sheafifiedExteriorPieceIso (p + q - 1)).hom.val.app U)) _ _) ?_)
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans (congrArg ((A.sheafifiedExteriorPieceIso (p + q - 1)).hom.val.app U)
      (Stacks.gradedCast_eq_degCast hA _)) ?_
    refine Eq.trans (Stacks.degCast_map
      (fun k => (A.sheafifiedExteriorPieceIso k).hom.val.app U) hA _).symm ?_
    refine congrArg (Stacks.degCast hA) ?_
    refine Eq.trans (A.sheafifiedExteriorPieceIso_mul (p - 1) q U _ y) ?_
    exact congrArg (fun t => (A.exterior.mul (p - 1) q).app U t
      ((A.sheafifiedExteriorPieceIso q).hom.val.app U y))
      (K.hom_app_sheafifiedD_d hp U x)
  · refine Eq.trans (map_zsmul
      (ConcreteCategory.hom ((A.sheafifiedExteriorPieceIso (p + q - 1)).hom.val.app U))
      (Int.negOnePow p : ℤ) _) ?_
    refine congrArg (fun t => (Int.negOnePow p : ℤ) • t) ?_
    refine Eq.trans (congrArg ((A.sheafifiedExteriorPieceIso (p + q - 1)).hom.val.app U)
      (Stacks.gradedCast_eq_degCast hB _)) ?_
    refine Eq.trans (Stacks.degCast_map
      (fun k => (A.sheafifiedExteriorPieceIso k).hom.val.app U) hB _).symm ?_
    refine congrArg (Stacks.degCast hB) ?_
    refine Eq.trans (A.sheafifiedExteriorPieceIso_mul p (q - 1) U x _) ?_
    exact congrArg ((A.exterior.mul p (q - 1)).app U
      ((A.sheafifiedExteriorPieceIso p).hom.val.app U x))
      (K.hom_app_sheafifiedD_d hq U y)

/-- **The transported differential takes a degree-one generator to the scalar `φ` assigns to
it.** This is the second hypothesis of the uniqueness half of Stacks tag 062K, for the functional
attached to `φ`. -/
theorem sheafifiedD_generator (U : Cᵒᵖ) (e : F.val.obj U) :
    (SheafOfModules.sheafifiedExteriorPieceZeroIso J F).hom.val.app U
        ((K.sheafifiedD (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e)) =
      (Stacks.SheafOfModules.unitExteriorFunctional φ).dual U e := by
  have hgen : (A.sheafifiedExteriorPieceIso 1).hom.val.app U
      ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e) =
        A.exteriorGenerator.val.app U e :=
    Eq.trans (SheafOfModules.comp_val_app_apply _ _ U e).symm
      (SheafOfModules.hom_congr_app_apply A.sheafifiedExteriorPieceIso_generator U e)
  have hval : (K.sheafifiedD (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
      ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e) =
        Stacks.RegularSequence.unitScalar φ U e •
          (SheafOfModules.sheafifiedExteriorAlgebra J F).one.eval U := by
    refine Eq.trans (K.sheafifiedD_app _ U _) ?_
    refine Eq.trans (congrArg ((A.sheafifiedExteriorPieceIso 0).inv.val.app U)
      (Eq.trans (congrArg (fun t => (t.val.app U)
          ((A.sheafifiedExteriorPieceIso 1).hom.val.app U
            ((SheafOfModules.sheafifiedExteriorGenerator J F).val.app U e)))
        (K.dOf_eq_d (show (1 : ℤ) - 1 + 1 = 1 by ring)))
        (Eq.trans (congrArg ((K.d 1).val.app U) hgen) (K.d_exteriorGenerator U e)))) ?_
    exact Eq.trans
      (map_smul (ConcreteCategory.hom ((A.sheafifiedExteriorPieceIso 0).inv.val.app U))
        (Stacks.RegularSequence.unitScalar φ U e) _)
      (congrArg (fun t => Stacks.RegularSequence.unitScalar φ U e • t)
        (A.sheafifiedExteriorPieceIso_inv_one U))
  have hkos := SheafOfModules.koszulD_exteriorGenerator J F
    (Stacks.SheafOfModules.unitExteriorFunctional φ) U e
  exact Eq.trans (congrArg
    ((SheafOfModules.sheafifiedExteriorPieceZeroIso J F).hom.val.app U)
    (Eq.trans hval (SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit
      (SheafOfModules.sheafifiedExteriorAlgebra J F)
      (SheafOfModules.sheafifiedExteriorPieceZeroIso J F)
      (SheafOfModules.sheafifiedExteriorPieceZeroIso_one J F) U _ _ hkos))) hkos

/-- **The transported differential is the Koszul differential of the functional attached to
`φ`**, by the uniqueness half of Stacks tag 062K. -/
theorem sheafifiedD_eq_koszulD {p q : ℤ} (h : q + 1 = p) :
    K.sheafifiedD h =
      SheafOfModules.koszulD J F (Stacks.SheafOfModules.unitExteriorFunctional φ) h :=
  SheafOfModules.koszulD_unique J F (Stacks.SheafOfModules.unitExteriorFunctional φ)
    (fun _ _ h => K.sheafifiedD h) (fun U e => K.sheafifiedD_generator U e)
    K.isKoszulDerivation_sheafifiedD h

/-! ### The differential of the chain data is a Koszul differential -/

/-- **The chain data's differential is the Koszul differential of the functional attached to
`φ`**, on the exterior powers of the bundle. The chain data imposes only the graded Leibniz rule
and the value on a degree-one generator, and those already determine it. -/
theorem dOf_eq_koszulD {p q : ℤ} (h : q + 1 = p) :
    K.dOf h = A.koszulD (Stacks.SheafOfModules.unitExteriorFunctional φ) h := by
  have hcomp := K.sheafifiedD_eq_koszulD h
  rw [SheafOfModules.TensorExteriorSymmetricAlgebras.koszulD,
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra.koszulD, ← hcomp, sheafifiedD,
    SheafOfModules.TensorExteriorSymmetricAlgebras.sheafifiedExteriorPieceIso,
    SheafOfModules.TensorExteriorSymmetricAlgebras.sheafifiedExteriorPieceIso]
  simp

/-- The differential of the associated chain complex is the transported Koszul differential of
the functional attached to `φ`, on the terms of the complex. -/
theorem chain_d_eq_koszulD {p q : ℤ} (h : q + 1 = p) :
    K.chain.d p q = K.koszulD (Stacks.SheafOfModules.unitExteriorFunctional φ) h := by
  obtain rfl : q = p - 1 := by omega
  have hd := K.chain_d p
  rw [KoszulChainData.koszulD, ← K.dOf_eq_koszulD h, K.dOf_eq_d h, ← hd]
  simp [chainXIso]

end Transport

/-! ### The coordinate contractions are cocycles -/

section Cocycle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J
    (SheafOfModules.free (R := toRingCat J Osharp) ι)}
  {φ : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶
    SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A φ)

/-- **The coordinate contraction `δⱼ` anticommutes with the differential of the Koszul complex**,
the differential applied first, on the exterior powers. Together with
`Stacks.RegularSequence.KoszulChainData.coordKoszulD_comp_dOf_comm` this is the identity
`δⱼ d + d δⱼ = 0`. -/
theorem dOf_comp_coordKoszulD_comm (j : ι) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    K.dOf h ≫ A.coordKoszulD j h' = -(A.coordKoszulD j h ≫ K.dOf h') := by
  rw [K.dOf_eq_koszulD h, K.dOf_eq_koszulD h']
  exact A.coordKoszulD_comp_koszulD_comm j _ h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the differential of the Koszul complex**,
the contraction applied first, on the exterior powers. -/
theorem coordKoszulD_comp_dOf_comm (j : ι) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    A.coordKoszulD j h ≫ K.dOf h' = -(K.dOf h ≫ A.coordKoszulD j h') := by
  rw [K.dOf_eq_koszulD h, K.dOf_eq_koszulD h']
  exact A.koszulD_comp_coordKoszulD_comm j _ h h'

/-- **The coordinate contraction `δⱼ` is a cocycle: it anticommutes with the differential of the
Koszul complex**, on the terms of the complex, the contraction applied first. This is the identity
`δⱼ d + d δⱼ = 0` that makes `δⱼ` a degree-one chain map of the complex into itself. -/
theorem coordKoszulD_comp_chain_d_comm (j : ι) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    K.coordKoszulD j h ≫ K.chain.d q r = -(K.chain.d p q ≫ K.coordKoszulD j h') := by
  rw [K.chain_d_eq_koszulD h, K.chain_d_eq_koszulD h']
  exact K.koszulD_comp_coordKoszulD_comm j _ h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the differential of the Koszul complex**,
on the terms of the complex, the differential applied first. -/
theorem chain_d_comp_coordKoszulD_comm (j : ι) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    K.chain.d p q ≫ K.coordKoszulD j h' = -(K.coordKoszulD j h ≫ K.chain.d q r) := by
  rw [K.chain_d_eq_koszulD h, K.chain_d_eq_koszulD h']
  exact K.coordKoszulD_comp_koszulD_comm j _ h h'

end Cocycle

end Stacks.RegularSequence.KoszulChainData

end
