module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransportTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorOfPairs

/-!
# Transporting the trivialization of a tensor product of pairs

Let `(C₁, O₁)` and `(C₂, O₂)` be ringed sites and let `F : Mod(O₁) ⥤ Mod(O₂)` carry the structure
sheaf to the structure sheaf and tensor products to tensor products on objects, with all four
coherences that `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for.
A pair `(L, α)` — an invertible `O₁`-module with a trivialization of its `n`-th tensor power — is
carried by `F` to the pair whose module is `F L` and whose trivialization is

`(F L)^{⊗ n} ≅ F(L^{⊗ n}) ≅ F(O₁) ≅ O₂`,

the comparison of tensor powers of Tag 01CU followed by `F` of the trivialization and the unit
comparison.  This file shows that the transport is a *homomorphism* for the tensor product of
pairs: the transported trivialization of the tensor product pair is, across the object-level
comparison `F(L ⊗ M) ≅ F L ⊗ F M`, the tensor product
`Stacks.Cohomology.Torsors.Generators.tensorTriv` of the two transported trivializations.

Together with `Stacks.SheafOfModules.TensorPowerTransport.transportTriv_congr`, which is the same
statement for an isomorphism of pairs in place of a tensor product of pairs, this is what makes
the comparison map of Tag 040Q a homomorphism of abelian groups.

## Main definitions

* `Stacks.SheafOfModules.TensorPowerTransport.transportTriv`: the transported trivialization of a
  pair, as a type ascription at the ring sheaves of the two ringed sites.

## Main results

* `Stacks.SheafOfModules.TensorPowerTransport.transportTriv_tensor`: **the transported
  trivialization of a tensor product of pairs is the tensor product of the two transported
  trivializations.**
* `Stacks.SheafOfModules.TensorPowerTransport.unitComparison_rightUnitor`: the two object-level
  comparisons are compatible with the right unit constraint *at the structure sheaf itself*,
  which is the form the statement above needs.

## Implementation notes

The content is the chain

* `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor`, which crosses the
  splitting `(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}` of Tag 01CU past the transport;
* the interchange `(f ≫ f') ⊗ₘ (g ≫ g') = (f ⊗ₘ g) ≫ (f' ⊗ₘ g')`, which collects the two halves
  of the transported trivializations once the two transports it produces have cancelled against
  the two transports of the previous step;
* `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` at the two trivializations, which
  moves the tensor comparison from `(L^{⊗ n}, M^{⊗ n})` to `(O₁, O₁)`;
* `Stacks.SheafOfModules.TensorPowerTransport.unitComparison_rightUnitor`.

Both the chain and the purely monoidal step inside the last of those are stated as identities of
an abstract monoidal category — `transportTriv_tensor_core` and `tensorHom_rightUnitor_unit` —
exactly as the two monoidal identities of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerTransportTensorProduct.lean` are, and
for the same reason: there the objects carry no projections of a ringed site, so `rw` on the
monoidal lemmas fires, and the sheaf case is reached by `exact`, which elaborates at default
transparency.
Everything the functor is applied to enters the core as an opaque morphism of the target
category, so the core needs one category and one monoidal structure; and the monoidal unit enters
as an *arbitrary* object with an arbitrary contraction `U ⊗ U ⟶ U`.  That last point is not
cosmetic: identifying `SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)` with
`𝟙_` is a crossing that exhausts the heartbeat budget at `whnf` if it is left to happen inside the
application of the core, where it occurs four times over; it happens once, in the statement of
`Stacks.SheafOfModules.TensorPowerTransport.unitComparison_rightUnitor`, and everything the core
is applied to is spelled with `SheafOfModules.unit`, as the two trivializations are.

The category and its monoidal structure are *explicit* arguments of the core, and are supplied
as `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)` with
`Stacks.Cohomology.Torsors.Generators.ringedSiteModulesMonoidal`.  Left implicit, the category is
inferred from the first argument — a
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso`, whose type is stated over a sheaf
of rings and a sheaf condition — and comes out as
`SheafOfModules (TensorSheafification.structureSheaf X₂.O.obj _)`, at which spelling there is no
monoidal structure to find; the failure is then reported as a heartbeat timeout at `whnf` rather
than as the missing instance it is, because unification goes on trying to solve for it from the
goal.  Pinning the category alone is not enough: at the pinned spelling the monoidal structure is
a `local instance` of another module, and re-enabling it with `attribute [local instance]` leaves
it findable for `MonoidalCategoryStruct` but not for `MonoidalCategory` itself.

For the same reason each remaining crossing of the two spellings of one notion —
`Stacks.SheafOfModules.Invertible.tensorProductIso` against
`Stacks.Cohomology.Torsors.Generators.tensorIsoOfModules`, and `F` of a composite against the
composite of its images — is made inside its own private lemma, `tensorIso_naturality'` and
`map_tensorTriv_hom`: recursion depth is counted on top of the enclosing elaboration, so a crossing
that is cheap on its own is not cheap inside the application of the core.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.Torsors.Generators (tpow tpowTensorIso tensorIsoOfModules
  tensorSheafOfModules powerMap tensorTriv)
open Stacks.SheafOfModules (IsInvertible)

universe w v₁ u₁ v₂ u₂ v u

namespace Stacks.SheafOfModules.TensorPowerTransport

/-- **The right unit constraint at the monoidal unit crosses a morphism to the unit.**  For
`h : A ⟶ 𝟙_`, tensoring `h` with itself and contracting the right-hand unit is the same as
tensoring `h` on the right only, contracting, and applying `h`.  A purely monoidal identity,
stated here so that `rw` meets objects carrying no projections of a ringed site. -/
private theorem tensorHom_rightUnitor_unit {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A : D} (h : A ⟶ 𝟙_ D) :
    (h ⊗ₘ h) ≫ (ρ_ (𝟙_ D)).hom = (𝟙 A ⊗ₘ h) ≫ (ρ_ A).hom ≫ h := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc,
    MonoidalCategory.rightUnitor_naturality, MonoidalCategory.id_tensorHom]

/-- **The transport of a tensor product of trivializations, as an identity of an abstract
monoidal category.**  The four hypotheses are the splitting of the tensor power of a tensor
product crossed past the transport, the naturality of the tensor comparison at the two
trivializations, the right unit constraint at the structure sheaf, and the factorization of the
image of the trivialization of the tensor product pair.  Every morphism the transporting functor
is applied to enters as an opaque morphism, and the structure sheaf of the target enters as an
arbitrary object `U` with an arbitrary contraction `U ⊗ U ⟶ U`. -/
private theorem transportTriv_tensor_core (D : Type u) [Category.{v} D]
    [mono : MonoidalCategory D]
    {T Z V W WU FA FB TA TB FU U : D}
    (p : V ≅ T) (pa : FA ≅ TA) (pb : FB ≅ TB)
    (ftt : V ⟶ W) (ht : W ⟶ FA ⊗ FB) (pm : T ⟶ Z) (tt₂ : Z ⟶ TA ⊗ TB)
    (fab : W ⟶ WU) (htu : WU ⟶ FU ⊗ FU) (fru : WU ⟶ FU) (ftm : V ⟶ FU)
    (ua : FA ⟶ FU) (ub : FB ⟶ FU) (hu : FU ⟶ U) (r : U ⊗ U ⟶ U)
    (hPT : ftt ≫ ht ≫ (pa.hom ⊗ₘ pb.hom) = p.hom ≫ pm ≫ tt₂)
    (hN : fab ≫ htu = ht ≫ (ua ⊗ₘ ub))
    (hU : htu ≫ (hu ⊗ₘ hu) ≫ r = fru ≫ hu)
    (hftm : ftm = ftt ≫ fab ≫ fru) :
    pm ≫ ((tt₂ ≫ (((pa.inv ≫ ua) ≫ hu) ⊗ₘ ((pb.inv ≫ ub) ≫ hu))) ≫ r) =
      (p.inv ≫ ftm) ≫ hu := by
  have hid : ∀ {Y : D} (z : (FA ⊗ FB) ⟶ Y),
      (pa.hom ⊗ₘ pb.hom) ≫ (pa.inv ⊗ₘ pb.inv) ≫ z = z := by
    intro Y z
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, pa.hom_inv_id,
      pb.hom_inv_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
  have hsplit : (((pa.inv ≫ ua) ≫ hu) ⊗ₘ ((pb.inv ≫ ub) ≫ hu)) =
      (pa.inv ⊗ₘ pb.inv) ≫ (ua ⊗ₘ ub) ≫ (hu ⊗ₘ hu) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  have hpm : pm ≫ tt₂ = p.inv ≫ ftt ≫ ht ≫ (pa.hom ⊗ₘ pb.hom) := by
    rw [hPT, p.inv_hom_id_assoc]
  rw [hftm, hsplit]
  simp only [Category.assoc]
  rw [← Category.assoc pm tt₂, hpm]
  simp only [Category.assoc]
  rw [hid, ← Category.assoc ht (ua ⊗ₘ ub), ← hN, Category.assoc, hU]

section RingedSites

variable (X₁ : RingedSite.{u₁, v₁, w})
    [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X₁.J AddCommGrpCat.{w}]
    (X₂ : RingedSite.{u₂, v₂, w})
    [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X₂.J AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))

-- The monoidal and symmetric structures used are the very `local instance`s of
-- `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfATensorProduct`, re-enabled
-- rather than redeclared: a defeq but syntactically different instance term would stop the
-- lemmas imported from that file from rewriting.
attribute [local instance] Stacks.Cohomology.Torsors.Generators.ringedSiteModulesMonoidal
  Stacks.Cohomology.Torsors.Generators.ringedSiteModulesSymmetric

/-- **The two object-level comparisons are compatible with the right unit constraint at the
structure sheaf.**  This is
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor` read at the structure sheaf
itself, where the whiskering of the unit comparison becomes a full tensor product of it with
itself by `Stacks.SheafOfModules.TensorPowerTransport.tensorHom_rightUnitor_unit`. -/
theorem unitComparison_rightUnitor
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hrunit : TensorIsoRightUnitor X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2
      X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten) :
    (hten (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom ≫
        ((tensorIsoOfModules X₂
            (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
              SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))
            (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
              SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom) =
      F.map (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom ≫
        hunit.hom := by
  have hcross : (tensorIsoOfModules X₂
        (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))
        (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom ≫
        (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom =
      (tensorIsoOfModules X₂
          (Iso.refl (F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))))
          (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
            SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom ≫
        (ρ_ (F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
          hunit.hom :=
    tensorHom_rightUnitor_unit _
  have hru : F.map (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom =
      (hten (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom ≫
        ((tensorIsoOfModules X₂
            (Iso.refl (F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))))
            (hunit : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ≅
              SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom ≫
          (ρ_ (F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom) :=
    hrunit (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
  -- The goal is type-correct only at default transparency, so `rw` refuses on it; the
  -- reassociations are made as terms.
  refine Eq.trans (congrArg (fun z =>
    (hten (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom ≫ z)
    (hcross.trans (Category.assoc _ _ _).symm)) ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ hunit.hom) hru.symm)

/-- The naturality of the object-level tensor comparison, read through
`Stacks.Cohomology.Torsors.Generators.tensorIsoOfModules` and the monoidal tensor product of
morphisms rather than through `Stacks.SheafOfModules.Invertible.tensorProductIso`.  This is
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` itself; naming it keeps the
crossing of the two spellings out of the application of
`transportTriv_tensor_core`. -/
private theorem tensorIso_naturality'
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hnat : TensorIsoNatural X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    {A B A' B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)} (e : A ≅ A')
    (f : B ≅ B') :
    F.map (tensorIsoOfModules X₁ e f).hom ≫ (hten A' B').hom =
      (hten A B).hom ≫ (F.map e.hom ⊗ₘ F.map f.hom) :=
  hnat A B A' B' e f

omit [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X₂.J AddCommGrpCat.{w}] in
/-- The image of the trivialization of a tensor product pair, as the composite of the images of
its three constituents.  Naming it keeps `CategoryTheory.Functor.map_comp` out of the application
of `transportTriv_tensor_core`. -/
private theorem map_tensorTriv_hom
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 M] (n : ℕ)
    (al : tpow X₁ L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    (bl : tpow X₁ M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) :
    F.map (tensorTriv X₁ L M n al bl).hom =
      F.map (tpowTensorIso X₁ L M n).hom ≫ F.map (tensorIsoOfModules X₁ al bl).hom ≫
        F.map (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom := by
  change F.map (((tpowTensorIso X₁ L M n).hom ≫ (tensorIsoOfModules X₁ al bl).hom) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom) = _
  refine Eq.trans (F.map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z =>
    z ≫ F.map (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom)
    (F.map_comp _ _)) ?_
  exact Category.assoc _ _ _

/-- **The transported trivialization of a pair**: the comparison of tensor powers of Tag 01CU,
`F` of the trivialization, and the unit comparison.  This is a type ascription, at the ring
sheaves of the two ringed sites, of the composite that `AlgebraicGeometry.basePairTriv` is for
the associated-module functor. -/
abbrev transportTriv
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L] (n : ℕ)
    (al : tpow X₁ L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) :
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
    tpow X₂ (F.obj L) n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) :=
  letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
  ((powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L n).symm ≪≫
    F.mapIso al) ≪≫ hunit

/-- **The transported trivialization of a tensor product of pairs is the tensor product of the
two transported trivializations**, across the object-level tensor comparison
`F(L ⊗ M) ≅ F L ⊗ F M`.

This is the tensor-product counterpart of
`Stacks.SheafOfModules.TensorPowerTransport.transportTriv_congr`, and it is what makes the
comparison map of Tag 040Q additive. -/
theorem transportTriv_tensor
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hnat : TensorIsoNatural X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hassoc : TensorIsoAssociator X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2
      X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hbraid : TensorIsoBraiding X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2
      X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hrunit : TensorIsoRightUnitor X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2
      X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten)
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 M] (n : ℕ)
    (al : tpow X₁ L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    (bl : tpow X₁ M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) :
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten M
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
      (tensorSheafOfModules X₁ L M)
    letI := Stacks.SheafOfModules.isInvertible_tensorSheaf X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L) (F.obj M)
    powerMap X₂ (hten L M) n ≪≫
          tensorTriv X₂ (F.obj L) (F.obj M) n
            (transportTriv X₁ X₂ F hunit hten L n al)
            (transportTriv X₁ X₂ F hunit hten M n bl) =
        transportTriv X₁ X₂ F hunit hten (tensorSheafOfModules X₁ L M) n
          (tensorTriv X₁ L M n al bl) := by
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten M
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
    (tensorSheafOfModules X₁ L M)
  let := Stacks.SheafOfModules.isInvertible_tensorSheaf X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L) (F.obj M)
  refine Iso.ext ?_
  refine transportTriv_tensor_core
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))
    (mono := Stacks.Cohomology.Torsors.Generators.ringedSiteModulesMonoidal X₂)
    (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
      (tensorSheafOfModules X₁ L M) n)
    (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L n)
    (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten M n)
    (F.map (tpowTensorIso X₁ L M n).hom)
    (hten (tpow X₁ L n) (tpow X₁ M n)).hom
    (powerMap X₂ (hten L M) n).hom
    (tpowTensorIso X₂ (F.obj L) (F.obj M) n).hom
    (F.map (tensorIsoOfModules X₁ al bl).hom)
    (hten (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom
    (F.map (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom)
    (F.map (tensorTriv X₁ L M n al bl).hom)
    (F.map al.hom) (F.map bl.hom)
    (hunit.hom : F.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))
    (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))).hom
    ?_ ?_ ?_ ?_
  · exact powerTransportIso_tensor X₁ X₂ F hunit hten hnat hassoc hbraid hrunit L M n
  · exact tensorIso_naturality' X₁ X₂ F hten hnat al bl
  · exact unitComparison_rightUnitor X₁ X₂ F hunit hten hrunit
  · exact map_tensorTriv_hom X₁ X₂ F L M n al bl

end RingedSites

end Stacks.SheafOfModules.TensorPowerTransport

end
