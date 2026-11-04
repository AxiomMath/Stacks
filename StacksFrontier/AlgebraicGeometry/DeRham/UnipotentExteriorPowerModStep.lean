module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth
public import StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModFirstStep
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsSplittingDependence

/-!
# A unipotent exterior power, modulo one more step of the wedge filtration

Let `iF : F ⟶ H` be a morphism of sheaves of modules, `w : H ⟶ F` arbitrary, and let
`θ = 𝟙 + w ≫ iF`, the shape of an endomorphism of `H` differing from the identity by a morphism
factoring through `iF`. By `SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id`,
`⋀ⁿθ` is the identity modulo the *first* step `F¹⋀ⁿH = Im(⋀¹F ⊗ ⋀^{n-1}H ⟶ ⋀ⁿH)` of the wedge
filtration. The identification of the graded pieces of Section 0FMK needs the stronger
statement one step up: for every `k`, `⋀ⁿθ` is the identity on `F^k⋀ⁿH` modulo `F^{k+1}⋀ⁿH`.

**This file proves that statement.** Under the one extra hypothesis the application supplies —
`iF ≫ w = 0`, i.e. `θ` fixes `iF` — the identity

`prodWedgeHom k q ≫ (⋀^{k+q}θ - 𝟙) = (𝟙_{⋀^kF} ⊗ (⋀^qθ - 𝟙)) ≫ prodWedgeHom k q`

holds: on a product `(⋀^kiF)(a) · b` the endomorphism `θ` moves only the second factor, because
it fixes the first. (The hypothesis is needed: `θ` must carry `F^k` into itself before it can
induce anything on `F^k/F^{k+1}`, and for `k ≥ 1` it does so only because it fixes the `k`
factors of `F`.) In the application `θ` is the transition automorphism between two splittings of
a short exact sequence, `CategoryTheory.ShortComplex.Splitting.transition`, and the hypothesis is
the composite `T.f ≫ T.g = 0`.

Combined with `SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id`, which says that
`⋀^qθ - 𝟙` factors through the first step of the filtration of `⋀^qH`, that identity reduces the
mod-`F^{k+1}` statement to the assertion that wedging the first step of `⋀^{1+m}H` with `⋀^kF`
lands in `F^{k+1}⋀ⁿH` — which is the associativity square
`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one`, whose other leg factors through
`⋀^{k+1}F ⊗ ⋀^mH ⟶ ⋀ⁿH`, read after the associator.

The total degree is written `k + 1 + m`, with `n - k = 1 + m`: that is the spelling in which the
first-step statement `SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id` and the
associativity square are both available with a single transport between `k + (1 + m)` and
`k + 1 + m`, which is `SheafOfModules.eqToHom_addAssoc_comp_eqToHom`.

## Main results

* `SheafOfModules.comp_unipotent_of_comp_eq_zero`: `θ` fixes `iF` when `iF ≫ w = 0`.
* `SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id`: **the identity above**, in the
  spelling of the tensor-product bifunctor.
* `SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id'`: the same in the left-whiskering
  spelling of the monoidal structure of [Stacks, Tag 01CA], which is the one the associativity
  square is stated in.
* `SheafOfModules.eqToHom_addAssoc_comp_eqToHom`: the two transports of the total degree between
  its spellings `k + (1 + m)` and `k + 1 + m` — the one the associativity square carries and the
  one `SheafOfModules.prodWedgeHomOfEq` carries — cancel.
* `SheafOfModules.epi_whiskerLeft_of_epi`: the tensor product of sheaves of modules is right
  exact in its second variable.
* `SheafOfModules.whiskerLeft_comp_eq_zero_of_eq_comp`: a left-whiskered morphism which factors
  dies against anything the whiskered second factor dies against.
* `SheafOfModules.whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ` and
  `SheafOfModules.whiskerLeft_imageSubobject_arrow_comp_prodWedgeHom_comp_cokernelπ`: **wedging
  the first step of the filtration of `⋀^{1+m}H` with `⋀^kF` lands in the `(k+1)`-st step of the
  filtration of `⋀^{k+1+m}H`**, for the wedge map itself and for its image subobject.
* `SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ` and
  `SheafOfModules.factors_imageSubobject_prodWedgeHom_comp_pieceMap_unipotent_sub_id`:
  **`⋀ⁿθ` is the identity on `F^k⋀ⁿH` modulo `F^{k+1}⋀ⁿH`**, in the cokernel form and in the
  image-subobject form.
* `SheafOfModules.prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ`: the same at the
  transition automorphism of two splittings of a short complex, where the hypothesis
  `iF ≫ w = 0` is the composite of the complex and so is discharged.

## Implementation notes

The hypothesis `iF ≫ w = 0` enters only through
`SheafOfModules.comp_unipotent_of_comp_eq_zero`, and through it only to know that `θ` fixes the
map `⋀^k F ⟶ ⋀^k H` induced by `iF`.

The first identity is proved on local pure tensors, by `PresheafOfModules.tensorSheaf_hom_ext`:
the comparison homomorphism `⋀F ⟶ ⋀H` induced by `iF` preserves products, so `⋀^{k+q}θ` of a
product is the product of `⋀^kθ` and `⋀^qθ` of the factors, and on the first factor `⋀^kθ` is
the identity. No computation in the ungraded realization `Stacks.GradedAlgebra.Total` is needed:
that computation is the one behind
`SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id`, and this file only transports
its conclusion along one factor of a tensor product.

**The composites are assembled in term mode, one step per declaration.** A source of the shape
`⋀^kF ⊗ ⋀^qH` is written by the monoidal structure as `tensorObj` and by
`SheafOfModules.prodWedgeHom` as `tensorSheafBifunctor.obj`; the two agree only up to unfolding
the monoidal structure, so a goal mixing them is not type-correct at the transparency `rw` and
`simp` check their motives at, and every rewrite on such a goal fails. Each step is therefore an
explicit `Eq.trans` of `Category.assoc` and `congrArg`, and the chain is cut into named lemmas so
that no single declaration crosses the unfolding more than a few times.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace Opposite

/-! The monoidal structure of [Stacks, Tag 01CA] on sheaves of modules over the ring sheaf
underlying a sheaf of commutative rings is `SheafOfModules.monoidalSheaves`; it is reused here
rather than restated, so that `⊗` and `◁` below are the very ones the wedge filtration and
its associativity square are built from. -/
attribute [local instance] SheafOfModules.monoidalSheaves

/-! That monoidal structure is indexed by `CategoryTheory.Sheaf.toRingCat`, while the objects
`Stacks.SheafOfModules.Tensor.sheafTensor` produces are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are the same bundled sheaf of rings, but
`ringSheaf` is an opaque `def`, so a hom type that mixes the two -- as every one below does,
having `⊗` on the left and a `sheafTensor` object on the right -- is not recognised as living in
the abelian category pinned further down, and loses its zero morphism. Making `ringSheaf`
reducible for implicit-argument unification identifies them at no further cost. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace SheafOfModules

open MonoidalCategory

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **A unipotent endomorphism `θ = 𝟙 + w ≫ iF` fixes `iF`** as soon as `iF ≫ w = 0`. In the
application `iF` and `w` are the inclusion of the sub of a short exact sequence and a morphism
factoring through its quotient, and the hypothesis is the composite of the sequence. -/
theorem comp_unipotent_of_comp_eq_zero (iF : F ⟶ H) (w : H ⟶ F) (hw : iF ≫ w = 0) :
    iF ≫ (𝟙 H + w ≫ iF) = iF := by
  rw [Preadditive.comp_add, Category.comp_id, ← Category.assoc, hw, zero_comp, add_zero]

/-- **A unipotent endomorphism moves only the second factor of a wedge product whose first
factor comes from `F`.** For `θ = 𝟙 + w ≫ iF` with `iF ≫ w = 0`,

`prodWedgeHom k q ≫ (⋀^{k+q}θ - 𝟙) = (𝟙_{⋀^kF} ⊗ (⋀^qθ - 𝟙)) ≫ prodWedgeHom k q`.

On a pure tensor `a ⊗ b` both sides are `(⋀^kiF)(a) · (⋀^qθ(b) - b)`: the comparison
homomorphism `⋀F ⟶ ⋀H` induced by `iF` preserves products, so `⋀^{k+q}θ` of the product is the
product of `⋀^kθ((⋀^kiF)(a))` with `⋀^qθ(b)`, and the first of these is `(⋀^kiF)(a)` again
because `θ` fixes `iF` (`SheafOfModules.comp_unipotent_of_comp_eq_zero`). -/
theorem prodWedgeHom_comp_pieceMap_unipotent_sub_id (iF : F ⟶ H) (w : H ⟶ F)
    (hw : iF ≫ w = 0) (k q : ℕ) :
    prodWedgeHom AF A A iF (𝟙 H) k q ≫
        (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
            ((k + q : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + q))) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((𝟙 (AF.exteriorPower k),
              A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
                  (q : ℤ) - 𝟙 (A.exteriorPower q)) :
            (AF.exteriorPower k, A.exteriorPower q) ⟶ (AF.exteriorPower k, A.exteriorPower q)) ≫
        prodWedgeHom AF A A iF (𝟙 H) k q := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) fun U a b => ?_
  -- the map on `⋀^kF` induced by `iF`, and the one on `⋀^qH` induced by `θ`
  have hfix : ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
          (𝟙 H + w ≫ iF)).app (k : ℤ)).val.app U
        (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
          (k : ℤ)).val.app U a) =
      ((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
        (k : ℤ)).val.app U a := by
    have h := AF.exterior_isExteriorAlgebra.pieceMap_comp A.exterior_isExteriorAlgebra
      A.exterior_isExteriorAlgebra iF (𝟙 H + w ≫ iF) (k : ℤ)
    rw [comp_unipotent_of_comp_eq_zero iF w hw] at h
    exact congrArg (fun m : AF.exteriorPower k ⟶ A.exteriorPower k => m.val.app U a) h.symm
  -- the left-hand side
  have hLval : (prodWedgeHom AF A A iF (𝟙 H) k q ≫
          (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
              ((k + q : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + q)))).val.app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k) (A.exteriorPower q)).app U
          (a ⊗ₜ b)) =
      (A.exterior.mul (k : ℤ) (q : ℤ)).app U
          (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
            (k : ℤ)).val.app U a)
          (((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
            (𝟙 H + w ≫ iF)).app (q : ℤ)).val.app U b) -
        (A.exterior.mul (k : ℤ) (q : ℤ)).app U
          (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
            (k : ℤ)).val.app U a) b := by
    have hstep : (prodWedgeHom AF A A iF (𝟙 H) k q ≫
            (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
                ((k + q : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + q)))).val.app U
          ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k) (A.exteriorPower q)).app U
            (a ⊗ₜ b)) =
        ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
              (𝟙 H + w ≫ iF)).app ((k : ℤ) + (q : ℤ))).val.app U
            ((A.exterior.mul (k : ℤ) (q : ℤ)).app U
              (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
                (k : ℤ)).val.app U a) b) -
          (A.exterior.mul (k : ℤ) (q : ℤ)).app U
            (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
              (k : ℤ)).val.app U a) b := by
      have h := prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF k q U a b
      exact congrArg (fun z => ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
        (𝟙 H + w ≫ iF)).app ((k : ℤ) + (q : ℤ))).val.app U z - z) h
    refine hstep.trans ?_
    refine congrArg (fun z => z - (A.exterior.mul (k : ℤ) (q : ℤ)).app U
      (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
        (k : ℤ)).val.app U a) b) ?_
    refine Eq.trans ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
      (𝟙 H + w ≫ iF)).map_mul (k : ℤ) (q : ℤ) U _ b) ?_
    exact congrArg (fun z => (A.exterior.mul (k : ℤ) (q : ℤ)).app U z
      (((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
        (𝟙 H + w ≫ iF)).app (q : ℤ)).val.app U b)) hfix
  -- the right-hand side
  have hRval : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
            ((𝟙 (AF.exteriorPower k),
                A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
                    (𝟙 H + w ≫ iF) (q : ℤ) - 𝟙 (A.exteriorPower q)) :
              (AF.exteriorPower k, A.exteriorPower q) ⟶
                (AF.exteriorPower k, A.exteriorPower q)) ≫
          prodWedgeHom AF A A iF (𝟙 H) k q).val.app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k) (A.exteriorPower q)).app U
          (a ⊗ₜ b)) =
      (A.exterior.mul (k : ℤ) (q : ℤ)).app U
        (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
          (k : ℤ)).val.app U a)
        (((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
              (𝟙 H + w ≫ iF)).app (q : ℤ)).val.app U b - b) := by
    have hmap := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
      (AF.exteriorPower k) (A.exteriorPower q) (𝟙 (AF.exteriorPower k))
      (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
        (q : ℤ) - 𝟙 (A.exteriorPower q)) U a b
    refine Eq.trans (congrArg ((prodWedgeHom AF A A iF (𝟙 H) k q).val.app U) hmap) ?_
    exact prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF k q U a _
  refine hLval.trans (Eq.trans ?_ hRval.symm)
  exact (map_sub ((A.exterior.mul (k : ℤ) (q : ℤ)).app U
    (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
      (k : ℤ)).val.app U a)) _ b).symm

/-- `SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id` in the left-whiskering spelling
of the monoidal structure of [Stacks, Tag 01CA], which is the one the associativity square
`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one` is stated in. -/
theorem prodWedgeHom_comp_pieceMap_unipotent_sub_id' (iF : F ⟶ H) (w : H ⟶ F)
    (hw : iF ≫ w = 0) (k q : ℕ) :
    prodWedgeHom AF A A iF (𝟙 H) k q ≫
        (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
            ((k + q : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + q))) =
      (AF.exteriorPower k ◁
          (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
            (q : ℤ) - 𝟙 (A.exteriorPower q))) ≫
        prodWedgeHom AF A A iF (𝟙 H) k q := by
  refine (prodWedgeHom_comp_pieceMap_unipotent_sub_id AF A iF w hw k q).trans ?_
  exact congrArg (fun φ : AF.exteriorPower k ⊗ A.exteriorPower q ⟶
      AF.exteriorPower k ⊗ A.exteriorPower q => φ ≫ prodWedgeHom AF A A iF (𝟙 H) k q)
    (Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
      (AF.exteriorPower k) _).symm

/-- **The two transports of the total degree cancel.** The associativity square
`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one` carries the transport from the spelling
`k + (1 + m)` of the total degree to the spelling `k + 1 + m`, and
`SheafOfModules.prodWedgeHomOfEq` carries the transport back; both are transports between two
spellings of one object, so their composite is the identity. -/
theorem eqToHom_addAssoc_comp_eqToHom (k m : ℕ) :
    eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
        eqToHom (congrArg (fun j : ℕ => A.exteriorPower j) (Nat.add_assoc k 1 m)) =
      𝟙 (A.exteriorPower (k + (1 + m))) :=
  (eqToHom_trans _ _).trans rfl

/-! ### The unipotent exterior power on one step of the filtration, modulo the next -/

/-! The cokernel and the image subobject below are taken in the abelian category of sheaves of
modules over the ring sheaf underlying `Osharp`. Searching for that from
`SheafOfModules.instAbelian` does not succeed at these binders, so
`Stacks.SheafOfModules.abelianOfSmallSite` — that same instance stated once with the
sheafification side conditions discharged — is turned on here rather than restated: it is then
the very instance the statement of
`SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id` is elaborated against. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite


/-- **Left whiskering preserves epimorphisms**: the tensor product of sheaves of modules of
[Stacks, Tag 01CA] is right exact in its second variable. -/
theorem epi_whiskerLeft_of_epi
    (P : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    {G G' : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (b : G ⟶ G') [Epi b] : Epi (P ◁ b) := by
  have hid : Epi (𝟙 P) := inferInstance
  have hb : Epi b := ‹Epi b›
  exact Eq.mpr (congrArg (fun φ => Epi φ)
      (Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp P b))
    (@Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map _ _
      (Opens.grothendieckTopology ↥X) _ _ _ Osharp _ _ _ _ _ (𝟙 P) b hid hb)

/-- **Wedging a degree-one factor of `F` into `⋀^{1+m}H` lands in the `(k+1)`-st step of the
wedge filtration of `⋀^{k+1+m}H`**, hence dies against the cokernel of
`⋀^{k+1}F ⊗ ⋀^mH ⟶ ⋀^{k+1+m}H`. This is the associativity square
`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one`, read after the associator: its other leg
factors through that morphism. -/
theorem whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ' (iF : F ⟶ H) (k m : ℕ) :
    ((AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫
        prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫
      Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 := by
  have hcok : prodWedgeHom AF A A iF (𝟙 H) (k + 1) m ≫
      Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 :=
    Limits.cokernel.condition _
  refine (Iso.cancel_iso_hom_left (α_ (AF.exteriorPower k) (AF.exteriorPower 1)
    (A.exteriorPower m)) _ _).1 (Eq.trans ?_ comp_zero.symm)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ Limits.cokernel.π
      (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
    (mulSheafTensorId_comp_prodWedgeHom_one AF A iF k m).symm).trans ?_
  exact (Category.assoc _ _ _).trans (by rw [hcok]; exact comp_zero)

/-- `SheafOfModules.whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ'`, reassociated. -/
theorem whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ (iF : F ⟶ H) (k m : ℕ) :
    (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫
        prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 :=
  by simpa only [Category.assoc] using
    whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ' AF A iF k m

/-- The first step of the wedge filtration of `⋀^{1+m}H`, wedged with `⋀^kF`, lands in the
`(k+1)`-st step of the wedge filtration of `⋀^{k+1+m}H`: the image-subobject form of
`SheafOfModules.whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ`, obtained from it by
cancelling the epimorphism onto the image, whiskered by `⋀^kF`. -/
theorem whiskerLeft_imageSubobject_arrow_comp_prodWedgeHom_comp_cokernelπ (iF : F ⟶ H)
    (k m : ℕ) :
    (AF.exteriorPower k ◁ (Limits.imageSubobject (prodWedgeHom AF A A iF (𝟙 H) 1 m)).arrow) ≫
        prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 := by
  have : Epi (AF.exteriorPower k ◁
      Limits.factorThruImageSubobject (prodWedgeHom AF A A iF (𝟙 H) 1 m)) :=
    epi_whiskerLeft_of_epi _ _
  refine zero_of_epi_comp (AF.exteriorPower k ◁ Limits.factorThruImageSubobject
    (prodWedgeHom AF A A iF (𝟙 H) 1 m)) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
      eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
        Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
    ((MonoidalCategory.whiskerLeft_comp (AF.exteriorPower k) _ _).symm.trans
      (congrArg (fun z => AF.exteriorPower k ◁ z)
        (Limits.imageSubobject_arrow_comp (prodWedgeHom AF A A iF (𝟙 H) 1 m))))).trans
    (whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ AF A iF k m)

/-- **Left whiskering a morphism that factors**: if `d = ψ ≫ ι` and `P ◁ ι` dies against a
morphism `W` out of `P ⊗ G'`, then so does `P ◁ d`. -/
theorem whiskerLeft_comp_eq_zero_of_eq_comp
    {P G G' G'' Q : SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    {d : G ⟶ G'} (ψ : G ⟶ G'') (ι : G'' ⟶ G') (hψ : ψ ≫ ι = d) (W : P ⊗ G' ⟶ Q)
    (hW : (P ◁ ι) ≫ W = 0) : (P ◁ d) ≫ W = 0 :=
  by rw [← hψ, MonoidalCategory.whiskerLeft_comp, Category.assoc, hW, comp_zero]

/-- **`⋀^{1+m}θ - 𝟙`, wedged with `⋀^kF`, lands in the `(k+1)`-st step of the wedge filtration
of `⋀^{k+1+m}H`.** For `θ = 𝟙 + w ≫ iF` the difference `⋀^{1+m}θ - 𝟙` factors through the first
step of the wedge filtration of `⋀^{1+m}H`
(`SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id`), and that first step wedged
with `⋀^kF` lands in the `(k+1)`-st step. No hypothesis on `w` is needed here. -/
theorem whiskerLeft_pieceMap_unipotent_sub_id_comp_prodWedgeHom_comp_cokernelπ (iF : F ⟶ H)
    (w : H ⟶ F) (k m : ℕ) :
    (AF.exteriorPower k ◁
        (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
          ((1 + m : ℕ) : ℤ) - 𝟙 (A.exteriorPower (1 + m)))) ≫
      prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
        eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 := by
  have hfac := factors_imageSubobject_pieceMap_unipotent_sub_id AF A iF w m
  exact whiskerLeft_comp_eq_zero_of_eq_comp
    ((Limits.imageSubobject (prodWedgeHom AF A A iF (𝟙 H) 1 m)).factorThru _ hfac)
    (Limits.imageSubobject (prodWedgeHom AF A A iF (𝟙 H) 1 m)).arrow
    (Subobject.factorThru_arrow _ _ hfac) _
    (whiskerLeft_imageSubobject_arrow_comp_prodWedgeHom_comp_cokernelπ AF A iF k m)

/-- **The exterior power of a unipotent endomorphism is the identity on the `k`-th step of the
wedge filtration modulo the `(k+1)`-st.** For `θ = 𝟙 + w ≫ iF` with `iF ≫ w = 0` and
`n = k + 1 + m`, the difference `⋀ⁿθ - 𝟙`, restricted along the morphism
`⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH` whose image is the `k`-th step, dies against the cokernel of
`⋀^{k+1}F ⊗ ⋀^mH ⟶ ⋀ⁿH`, whose image is the `(k+1)`-st.

On such a product `θ` moves only the second wedge factor
(`SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id'`), where `⋀^{1+m}θ - 𝟙` factors
through the first step of the wedge filtration of `⋀^{1+m}H`
(`SheafOfModules.factors_imageSubobject_pieceMap_unipotent_sub_id`), and wedging that first step
with `⋀^kF` lands in the `(k+1)`-st step. -/
theorem prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ (iF : F ⟶ H) (w : H ⟶ F)
    (hw : iF ≫ w = 0) (k m : ℕ) :
    prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
        (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
            ((k + (1 + m) : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + (1 + m)))) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) = 0 := by
  rw [← Category.assoc, prodWedgeHom_comp_pieceMap_unipotent_sub_id' AF A iF w hw k (1 + m),
    Category.assoc]
  exact whiskerLeft_pieceMap_unipotent_sub_id_comp_prodWedgeHom_comp_cokernelπ AF A iF w k m

/-- **The subobject form of
`SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ`.** On the `k`-th step
of the wedge filtration of `⋀^{k+1+m}H` the difference `⋀ⁿθ - 𝟙` factors through the `(k+1)`-st
step, written out as the image subobject of `⋀^{k+1}F ⊗ ⋀^mH ⟶ ⋀^{k+1+m}H` so that it does not
depend on any particular packaging of the filtration. -/
theorem factors_imageSubobject_prodWedgeHom_comp_pieceMap_unipotent_sub_id (iF : F ⟶ H)
    (w : H ⟶ F) (hw : iF ≫ w = 0) (k m : ℕ) :
    (Limits.imageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)).Factors
      (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
        (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H + w ≫ iF)
            ((k + (1 + m) : ℕ) : ℤ) - 𝟙 (A.exteriorPower (k + (1 + m)))) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) := by
  have hexact : Limits.imageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) =
      Limits.kernelSubobject (Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) :=
    (ShortComplex.exact_iff_image_eq_kernel
      (ShortComplex.mk (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)
        (Limits.cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
        (Limits.cokernel.condition _))).1 (ShortComplex.exact_cokernel _)
  rw [hexact]
  refine Limits.kernelSubobject_factors _ _ ?_
  rw [Category.assoc, Category.assoc]
  exact prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ AF A iF w hw k m

/-- **The exterior power of the transition automorphism of two splittings is the identity on
the `k`-th step of the wedge filtration modulo the `(k+1)`-st.** For a short complex
`0 ⟶ ℱ ⟶ ℋ ⟶ 𝒢 ⟶ 0` of sheaves of modules with two splittings `sp`, `sp'`, the automorphism `θ`
of `ℋ` carrying one to the other (`CategoryTheory.ShortComplex.Splitting.transition`) differs
from the identity by a morphism factoring through `ℱ ⟶ ℋ`, and that morphism is killed by
`ℱ ⟶ ℋ` because the complex composes to zero, so
`SheafOfModules.prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ` applies to it. -/
theorem prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ
    {T : ShortComplex
      (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))}
    (sp sp' : T.Splitting)
    (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₁)
    (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₂) (k m : ℕ) :
    prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) k (1 + m) ≫
        (A₂.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra
            (sp.transition sp') ((k + (1 + m) : ℕ) : ℤ) -
          𝟙 (A₂.exteriorPower (k + (1 + m)))) ≫
          eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            Limits.cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) = 0 := by
  have hθ : sp.transition sp' = 𝟙 T.X₂ + (-(T.g ≫ sp.s ≫ sp'.r)) ≫ T.f :=
    sub_eq_iff_eq_add'.1 (sp.transition_sub_id sp')
  have hw : T.f ≫ (-(T.g ≫ sp.s ≫ sp'.r)) = 0 := by
    rw [Preadditive.comp_neg, ← Category.assoc, T.zero, zero_comp, neg_zero]
  rw [hθ]
  exact prodWedgeHom_comp_pieceMap_unipotent_sub_id_comp_cokernelπ AF₁ A₂ T.f _ hw k m

end SheafOfModules

end
