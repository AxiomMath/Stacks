module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural
public import StacksFrontier.CategoryTheory.Trace.Sorites.TwistedRestrictionTrace

/-!
# The descent sheaf of `A[H]`, viewed over `A`, is `f_* A`

Let `f : V ⟶ X` be a Galois covering with finite group `H` and `A` a commutative ring.  The
sections over an étale `W ⟶ X` of the descent sheaf `D(A[H])` of
`AlgebraicGeometry.EtaleGaloisCovering.regularDescentSheaf` are the locally constant maps
`s : W ×_X V → A[H]` with `s(h · z) = s(z) h⁻¹`.  The map `s ↦ (z ↦ s(z)(1))` identifies them,
`A`-linearly and compatibly with restrictions, with all locally constant maps `W ×_X V → A`, the
sections of the direct image `f_* 𝓛_V(A)` of the sheaf of locally constant `A`-valued maps on
`V` (which is the constant sheaf `A`).  Its inverse is `t ↦ (z ↦ ∑_h t(h · z) h)`.

Under this identification, multiplication by `g⁻¹ ∈ H` on `D(A[H])` (an `A`-linear, not
`A[H]`-linear, endomorphism) is pulling back along the deck transformation `g`.

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.regularDescentRestrictScalarsIso`: the isomorphism
  `D(A[H])|_A ≅ f_* 𝓛_V(A)`.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.regularDescentRestrictScalarsHom_groupElementAction`:
  multiplication by `g⁻¹` on `D(A[H])` corresponds to pulling back along `g` on `f_* 𝓛_V(A)`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {A : Type} [CommRing A] {H : Type} [Group H] [Fintype H]
  (G : EtaleGaloisCovering X H)

/-- The restriction of scalars along `A → A[H]` of the descent sheaf of `A[H]`. -/
abbrev regularDescentRestrictScalars : EtaleModules.{u, 0} A X :=
  (etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := A) (M := H)) X).obj
    G.regularDescentSheaf

/-- The sheaf `f_* 𝓛_V(A)` of locally constant `A`-valued maps on the covering, pushed forward
to `X`. -/
abbrev coverLocallyConstantDirectImage : EtaleModules.{u, 0} A X :=
  (etaleModuleDirectImage.{u, 0} A G.cover.hom).obj
    (smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} A G.cover.left (ULift.{u + 1} A))

/-- The section `z ↦ ∑_h t(h · z) h` of the descent sheaf of `A[H]` attached to a locally
constant map `t : W ×_X V → A`. -/
def regularSectionOf {W : X.Etale} (t : LocallyConstant (G.fiberProd W) (ULift.{u + 1} A)) :
    LocallyConstant (G.fiberProd W) (ULift.{u + 1} (MonoidAlgebra A H)) :=
  ∑ h : H, LocallyConstant.map (fun a : ULift.{u + 1} A =>
      (ULift.up (MonoidAlgebra.single h a.down) : ULift.{u + 1} (MonoidAlgebra A H)))
    (LocallyConstant.comap (G.pullbackAct W h).base.hom t)

/-- The coefficient of `k` in `(∑_h t(h · z) h)` is `t(k · z)`. -/
theorem regularSectionOf_apply {W : X.Etale} (t : LocallyConstant (G.fiberProd W) (ULift.{u + 1} A))
    (z : G.fiberProd W) (k : H) :
    ((G.regularSectionOf t z).down).coeff k = (t ((G.pullbackAct W k).base z)).down := by
  classical
  have h₁ := map_sum (LocallyConstant.evalAddMonoidHom (Y := ULift.{u + 1} (MonoidAlgebra A H)) z)
    (fun c : H => LocallyConstant.map (fun a : ULift.{u + 1} A =>
      (ULift.up (MonoidAlgebra.single c a.down) : ULift.{u + 1} (MonoidAlgebra A H)))
      (LocallyConstant.comap (G.pullbackAct W c).base.hom t)) Finset.univ
  have h₂ := map_sum (AddEquiv.ulift : ULift.{u + 1} (MonoidAlgebra A H) ≃+ MonoidAlgebra A H)
    (fun c : H => (ULift.up (MonoidAlgebra.single c (t ((G.pullbackAct W c).base z)).down) :
      ULift.{u + 1} (MonoidAlgebra A H))) Finset.univ
  rw [regularSectionOf, ← LocallyConstant.evalAddMonoidHom_apply, h₁]
  change (AddEquiv.ulift (∑ c : H, (ULift.up (MonoidAlgebra.single c
    (t ((G.pullbackAct W c).base z)).down) : ULift.{u + 1} (MonoidAlgebra A H)))).coeff k = _
  rw [h₂, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  change ∑ c : H, (Finsupp.single c (t ((G.pullbackAct W c).base z)).down) k = _
  simp [Finsupp.single_apply]

/-- The section `z ↦ ∑_h t(h · z) h` is equivariant: it is a section of the descent sheaf of
`A[H]`. -/
theorem regularSectionOf_mem {W : X.Etale} (t : LocallyConstant (G.fiberProd W) (ULift.{u + 1} A)) :
    G.regularSectionOf t ∈ G.equivariantMaps (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H))
      (rightRegularRepULift.{u} A H) W := by
  intro h z
  ext k
  change ((G.regularSectionOf t ((G.pullbackAct W h).base z)).down).coeff k =
    ((G.regularSectionOf t z).down * MonoidAlgebra.single h⁻¹ 1).coeff k
  rw [MonoidAlgebra.coeff_mul_single_apply, inv_inv, mul_one, regularSectionOf_apply,
    regularSectionOf_apply, ← Scheme.Hom.comp_apply, ← G.pullbackAct_mul]

omit [Fintype H] in
/-- The value `s(z)(k)` of an equivariant section is the value `s(k · z)(1)`. -/
theorem coeff_eq_coeff_one_pullbackAct {W : X.Etale}
    (x : G.equivariantMaps (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H))
      (rightRegularRepULift.{u} A H) W) (z : G.fiberProd W) (k : H) :
    ((x.1 z).down).coeff k = ((x.1 ((G.pullbackAct W k).base z)).down).coeff 1 := by
  rw [x.2 k z]
  change _ = ((x.1 z).down * MonoidAlgebra.single k⁻¹ 1).coeff 1
  rw [MonoidAlgebra.coeff_mul_single_apply, inv_inv, one_mul, mul_one]

/-- **The sections of `D(A[H])|_A` as locally constant `A`-valued maps**: `s ↦ (z ↦ s(z)(1))`. -/
def regularSectionLinearMap (W : X.Etale) :
    (G.regularDescentRestrictScalars (A := A)).obj.obj (op W) →ₗ[A]
      LocallyConstant (G.fiberProd W) (ULift.{u + 1} A) where
  toFun x := LocallyConstant.map (fun y : ULift.{u + 1} (MonoidAlgebra A H) =>
      (ULift.up ((y.down).coeff 1) : ULift.{u + 1} A))
    (show G.equivariantMaps (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H))
      (rightRegularRepULift.{u} A H) W from x).1
  map_add' x y := by
    ext z
    change ((x.1 z).down + (y.1 z).down).coeff 1 = ((x.1 z).down).coeff 1 + ((y.1 z).down).coeff 1
    rw [MonoidAlgebra.coeff_add]
    rfl
  map_smul' a x := by
    ext z
    change (MonoidAlgebra.single 1 a * (x.1 z).down).coeff 1 = a * ((x.1 z).down).coeff 1
    rw [MonoidAlgebra.coeff_single_mul_apply, inv_one, one_mul]

omit [Fintype H] in
/-- The map `s ↦ (z ↦ s(z)(1))` evaluated at `s` and `z` is the coefficient of `1` in `s(z)`. -/
theorem regularSectionLinearMap_apply (W : X.Etale)
    (x : G.equivariantMaps (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H))
      (rightRegularRepULift.{u} A H) W) (z : G.fiberProd W) :
    ((G.regularSectionLinearMap W x) z).down = ((x.1 z).down).coeff 1 :=
  rfl

omit [Fintype H] in
/-- The map `s ↦ (z ↦ s(z)(1))` from sections of `D(A[H])|_A` over `W` to locally constant maps
`W ×_X V → A` is bijective. -/
theorem bijective_regularSectionLinearMap [Finite H] (W : X.Etale) :
    Function.Bijective (G.regularSectionLinearMap (A := A) W) := by
  have := Fintype.ofFinite H
  constructor
  · intro x y hxy
    apply Subtype.ext
    ext z k
    rw [G.coeff_eq_coeff_one_pullbackAct (A := A) x z k,
      G.coeff_eq_coeff_one_pullbackAct (A := A) y z k]
    exact congrArg ULift.down (DFunLike.congr_fun hxy ((G.pullbackAct W k).base z))
  · intro t
    refine ⟨⟨G.regularSectionOf t, G.regularSectionOf_mem t⟩, ?_⟩
    ext z
    change ((G.regularSectionOf t z).down).coeff 1 = (t z).down
    rw [regularSectionOf_apply, G.pullbackAct_one]
    rfl

/-- **`D(A[H])|_A ⟶ f_* 𝓛_V(A)`**, sectionwise `s ↦ (z ↦ s(z)(1))`. -/
def regularDescentRestrictScalarsHom :
    G.regularDescentRestrictScalars (A := A) ⟶ G.coverLocallyConstantDirectImage (A := A) where
  hom :=
    { app W := ModuleCat.ofHom (X := (G.regularDescentRestrictScalars (A := A)).obj.obj W)
        (Y := (G.coverLocallyConstantDirectImage (A := A)).obj.obj W)
        (G.regularSectionLinearMap (A := A) W.unop)
      naturality W W' g := by
        ext x
        refine LocallyConstant.ext fun z => ?_
        apply ULift.ext
        change ((x.1 ((G.pullbackMap g.unop).base z)).down).coeff 1 =
          ((x.1 (((Stacks.EtaleCohomology.smallEtaleBaseChange G.cover.hom).map
            g.unop).left.base z)).down).coeff 1
        rw [G.smallEtaleBaseChange_map_left]
        rfl }

omit [Fintype H] in
/-- The morphism `D(A[H])|_A ⟶ f_* 𝓛_V(A)` is an isomorphism. -/
instance isIso_regularDescentRestrictScalarsHom [Finite H] :
    IsIso (G.regularDescentRestrictScalarsHom (A := A)) :=
  isIso_of_bijective_app A (G.regularDescentRestrictScalarsHom (A := A))
    (fun W => G.bijective_regularSectionLinearMap W)

/-- **The descent sheaf of `A[H]`, viewed over `A`, is `f_* 𝓛_V(A)`.** -/
abbrev regularDescentRestrictScalarsIso :
    G.regularDescentRestrictScalars (A := A) ≅ G.coverLocallyConstantDirectImage (A := A) :=
  asIso (G.regularDescentRestrictScalarsHom (A := A))

omit [Fintype H] in
/-- **Multiplication by `g⁻¹` on `D(A[H])` is the deck transformation `g` on `f_* 𝓛_V(A)`.**
Under `s ↦ (z ↦ s(z)(1))`, the `A`-linear endomorphism `s ↦ g⁻¹ s` becomes pulling back along
the action of `g` on `W ×_X V`. -/
theorem regularDescentRestrictScalarsHom_groupElementAction [Finite H] (g : H) :
    (etaleModuleRestrictScalarsNatTrans (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
        (Stacks.Trace.groupElementAction.{0, 0, u + 1} A H g) X).app G.regularDescentSheaf ≫
        G.regularDescentRestrictScalarsHom (A := A) =
      G.regularDescentRestrictScalarsHom (A := A) ≫
        locallyConstantPushforwardMap A (ULift.{u + 1} A) G.cover.hom G.cover.hom (G.act g)
          (G.act_comp_hom g) := by
  have := Fintype.ofFinite H
  apply Sheaf.hom_ext
  ext W x
  refine LocallyConstant.ext fun z => ?_
  apply ULift.ext
  change ((MonoidAlgebra.single g⁻¹ 1 * (x.1 z).down)).coeff 1 =
    ((x.1 ((pullback.map W.unop.hom G.cover.hom W.unop.hom G.cover.hom (𝟙 _) (G.act g) (𝟙 _)
      (by simp) (by simp [G.act_comp_hom])).base z)).down).coeff 1
  rw [MonoidAlgebra.coeff_single_mul_apply, inv_inv, one_mul, mul_one]
  exact G.coeff_eq_coeff_one_pullbackAct (A := A) x z g

end AlgebraicGeometry.EtaleGaloisCovering

end
