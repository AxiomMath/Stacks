module

public import StacksCore.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The filtration of an exterior power by the images of a submodule

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `iF : F ⟶ H` a
morphism of sheaves of `O♯`-modules. Multiplying in the exterior algebra of `H` gives, for all
`k` and `q`, the wedge-product morphism

`⋀^k F ⊗_{O♯} ⋀^q H ⟶ ⋀^{k+q} H`

of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf`, and the images of
these morphisms with `k + q = n` filter `⋀ⁿ H`:

`F^k = Im (⋀^k F ⊗ ⋀^{n-k} H ⟶ ⋀ⁿ H)`.

**This file constructs that filtration and proves that it is one**: the steps decrease, the
zeroth step is all of `⋀ⁿ H` and the steps above `n` vanish. For the morphism
`f^*Ω_{Y/S} ⟶ Ω_{X/S}` of the transitivity sequence of a smooth morphism this is the filtration
of the single sheaf `Ω^n_{X/S}` whose graded pieces [Stacks, Section 0FMK] identifies, and the
last section instantiates it there.

The input the filtration needs, and which the repository did not have, is that the graded
multiplication of an exterior algebra is surjective in the last degree:

`⋀^k F ⊗ ⋀^1 F ⟶ ⋀^{k+1} F`  is an epimorphism.

This is proved first, stalkwise: the stalk of `⋀^{k+1}F` is `⋀^{k+1}` of the stalk of `F`
([Stacks, Tag 01CH]), which is spanned by wedges of `k + 1` germs, and such a wedge is the image
of the germ of a pure tensor of a wedge of `k` sections with one section — the ordered product of
`k + 1` degree-one sections of a graded algebra being the product of the first `k` of them with
the last.

## Main definitions

* `SheafOfModules.exteriorImageFiltration`: **the filtration** of `⋀ⁿ H` by the images of
  `⋀^k F ⊗ ⋀^{n-k} H`, as a family of subobjects of `⋀ⁿ H`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorFiltration`: the instance of that
  filtration at the transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`, i.e. **the
  filtration of `Ω^n_{X/S}` by the forms pulled back from `Y`.**

## Main results

* `SheafOfModules.GradedAlgebra.epi_mulSheaf_one_right`: **the graded multiplication
  `⋀^k ⊗ ⋀^1 ⟶ ⋀^{k+1}` of an exterior algebra is an epimorphism.**
* `SheafOfModules.prodWedgeHomIdRight_val_app_tensorSheafUnit`: the wedge-product morphism on a
  pure tensor of two arbitrary local sections, when the second structural morphism is the
  identity of `H`.
* `SheafOfModules.prodWedgeHom_eq_tensorSheafBifunctor_map_comp` and
  `SheafOfModules.prodWedgeHom_eq_whiskerLeft_pieceMap_comp`: the wedge-product morphism out of
  `⋀^pF ⊗ ⋀^qG` is the one out of `⋀^pF ⊗ ⋀^qH` precomposed with `⋀^q` of `G ⟶ H`, in the
  bifunctor and in the whiskering spelling.
* `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_id`: **the associativity square** when the
  second structural morphism is the identity of `H`, at an arbitrary degree of the factor that is
  moved. Multiplying two factors of `F` together and then wedging into `⋀ⁿ H` is the same as
  regrouping and wedging the `⋀^j F` factor into `⋀^p H` first.
  `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one` is its degree-one case, which is the one
  the step-by-one containment below consumes.
* `SheafOfModules.whiskerLeft_pieceMap_comp_associator_hom_comp`: **the interchange of the two
  whiskerings across the associator** — whiskering by `⋀^p(iG)` outside the regrouping is
  whiskering it into the inner wedge-product morphism.
* `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom`: **the associativity square at an arbitrary
  second structural morphism**, which is the form the graded pieces of [Stacks, Section 0FMK]
  need.
* `SheafOfModules.epi_mulSheafTensorId`: the multiplication of the exterior algebra of `F`,
  tensored with `⋀^p H`, is still an epimorphism.
* `SheafOfModules.exteriorImageFiltration_succ_le` and
  `SheafOfModules.exteriorImageFiltration_antitone`: **the filtration decreases.**
* `SheafOfModules.exteriorImageFiltration_zero`: **the filtration is exhaustive**: its zeroth
  step is all of `⋀ⁿ H`.
* `SheafOfModules.exteriorImageFiltration_eq_bot`: **the filtration vanishes above `n`.**
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorFiltration_spec`: the filtration of
  `Ω^n_{X/S}` is exhaustive and decreasing.

## Implementation notes

**Why the epimorphism is needed, and where.** The containment `F^{k+1} ≤ F^k` is not witnessed by
a morphism `⋀^{k+1}F ⊗ ⋀^{n-k-1}H ⟶ ⋀^k F ⊗ ⋀^{n-k}H`: there is none. What exists is the
commuting square `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one` over the common source
`(⋀^k F ⊗ ⋀^1 F) ⊗ ⋀^{n-k-1}H`, whose map onto `⋀^{k+1}F ⊗ ⋀^{n-k-1}H` is an epimorphism and
whose other leg factors through `⋀^k F ⊗ ⋀^{n-k}H`. Precomposition with an epimorphism does not
change an image, so the first image is the image of the common source, which is contained in the
second.

**The filtration is a `dite`, and its step above `n` is `⊥` by definition.** The image
description only makes sense for `k ≤ n`, where `n - k` is the complementary degree; above `n`
there is no wedge of `k` sections of `F` inside `⋀ⁿ H` and the step is `⊥`. The zeroth step is
*not* defined to be `⊤`: it is the image of `⋀^0 F ⊗ ⋀ⁿ H ⟶ ⋀ⁿ H`, and
`SheafOfModules.exteriorImageFiltration_zero` proves that image is everything, via
`SheafOfModules.oneTensorId_comp_prodWedgeHom` — the degree-zero wedge-product morphism, composed
with the global unit of the exterior algebra of `F`, is the left unitor.

**The monoidal structure is named once.** `Stacks.TensorSheafWorld.monoidalCategory` carries
three sheafification instances which instance search re-derives at every occurrence, exhausting
the synthesis budget; `SheafOfModules.monoidalSheaves` names it so that `⊗`, `◁`, `▷` and `α_`
below refer to it at no further cost. The same is done for the abelian structure, which the
images and the lattice of subobjects need.

**Morphism equalities are checked on local sections.** A morphism out of a tensor product sheaf
is not determined by its values on local pure tensors, but two morphisms agreeing on them are
equal (`PresheafOfModules.tensorSheaf_hom_ext` and, for a twice-iterated tensor product,
`PresheafOfModules.tensorSheaf_hom_ext₂`), and that is how the associativity square and the
degree-zero identification are proved — from the associativity and the unit law of the graded
algebra of `H` on local sections, exactly as `Stacks.TensorSheafWorld.mulSheaf_assoc` is.

**Why the associativity square at an arbitrary second structural morphism is a ladder and not one
declaration.** `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_id`, the case `iG = 𝟙 H` proved
on local sections, uses 190,550 of the 200,000 heartbeats of the default budget on its own, and
its statement alone — where a composite spelled with the tensor bifunctor of [Stacks, Tag 0GMW]
meets one spelled with the monoidal structure of [Stacks, Tag 01CA] — costs 71,044 of those. The
general case is therefore not reachable by adding the second structural morphism to that proof;
it is assembled formally from the case `iG = 𝟙 H` by
`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_eq_mulSheafTensorPieceMap`,
`SheafOfModules.mulSheafTensorPieceMap_eq_pieceMapRight_comp_mulSheafTensorId` — two steps of pure
bifunctoriality, so with no monoidal spelling in them at all — and
`SheafOfModules.whiskerLeft_pieceMap_comp_associator_hom_comp`, the interchange across the
associator. Every mixed-spelling composite in the chain costs tens of thousands of heartbeats, so
each step that contains one is a declaration of its own, and the steps that do not are written
with the bifunctor throughout.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SheafOfModules.SymPresentation

/-! The ring sheaf underlying `Osharp` has two spellings here: `CategoryTheory.Sheaf.toRingCat`,
which the module sheaves below are indexed by, and `Stacks.SheafOfModules.Tensor.ringSheaf`,
which `Stacks.SheafOfModules.Tensor.sheafTensor` is indexed by. The two are the same bundled
sheaf, but instance search does not unfold the second, so `◁` applied to an object produced by
`sheafTensor` does not find `SheafOfModules.monoidalSheaves` below. The monoidal structure at
that second spelling is `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf`, which is
deliberately not a global instance; the first line below is the opt-in its docstring asks for,
and it is what lets `◁` be applied to such an object. The second line is needed as well, and for
the converse direction: the images and subobjects below are formed in the abelian structure at
the *first* spelling, so a morphism whose source `sheafTensor` produced has to be recognised
there too, which `HasImage` cannot do while `ringSheaf` is opaque. -/
attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

/-! ### The multiplication of an exterior algebra is surjective in the last degree -/

namespace SheafOfModules.GradedAlgebra

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1)

/-- The stalk of the multiplication `A_k ⊗ A_1 ⟶ A_{k+1}` on the germ of a pure tensor of two
local sections is the germ of their product. -/
theorem stalkMapL_mulSheaf_tensorSheafGerm (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (a : (A.piece (k : ℤ)).val.obj (op U)) (b : (A.piece 1).val.obj (op U)) :
    PresheafOfModules.stalkMapL x (valHom (mulSheaf A (k : ℤ) 1))
        (PresheafOfModules.tensorSheafGerm Osharp (A.piece (k : ℤ)) (A.piece 1) x U hx a b) =
      TopCat.Presheaf.germ (A.piece ((k : ℤ) + 1)).val.presheaf U x hx
        ((A.mul (k : ℤ) 1).app (op U) a b) := by
  refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x (valHom (mulSheaf A (k : ℤ) 1)))
    (PresheafOfModules.tensorSheafGerm_eq Osharp (A.piece (k : ℤ)) (A.piece 1) x U hx a b)) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x (valHom (mulSheaf A (k : ℤ) 1)) U hx _) ?_
  exact congrArg (TopCat.Presheaf.germ (A.piece ((k : ℤ) + 1)).val.presheaf U x hx)
    (mulSheaf_unit A (k : ℤ) 1 (op U) a b)

variable (hA : IsExteriorAlgebra A gen)

/-- The germ of a wedge of `k + 1` local sections is in the image of the stalk of the
multiplication `A_k ⊗ A_1 ⟶ A_{k+1}`: peel the last factor. -/
theorem exteriorPowerStalkEquiv_stalkMapL_mulSheaf_ιMulti (k : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin (k + 1) → M.val.obj (op U)) :
    exteriorPowerStalkEquiv A gen hA (k + 1) x
        (PresheafOfModules.stalkMapL x (valHom (mulSheaf A (k : ℤ) 1))
          (PresheafOfModules.tensorSheafGerm Osharp (A.piece (k : ℤ)) (A.piece 1) x U hx
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) k
              fun i => gen.val.app (op U) (s i.castSucc))
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) 1
              fun _ => gen.val.app (op U) (s (Fin.last k))))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := by
  have happ : Fin.append (fun i : Fin k => gen.val.app (op U) (s i.castSucc))
        (fun _ : Fin 1 => gen.val.app (op U) (s (Fin.last k))) =
      fun i => gen.val.app (op U) (s i) := by
    rw [Fin.append_right_eq_snoc]
    exact Fin.snoc_init_self fun i => gen.val.app (op U) (s i)
  refine Eq.trans (congrArg (exteriorPowerStalkEquiv A gen hA (k + 1) x)
    (stalkMapL_mulSheaf_tensorSheafGerm A k x U hx _ _)) ?_
  refine Eq.trans (congrArg
    (fun y => exteriorPowerStalkEquiv A gen hA (k + 1) x
      (TopCat.Presheaf.germ (A.piece ((k : ℤ) + 1)).val.presheaf U x hx y))
    ((Stacks.GradedAlgebra.mul_homogeneousProd A.toPresheafGradedAlgebra (op U) k 1 _ _).trans
      (congrArg (A.toPresheafGradedAlgebra.homogeneousProd (op U) (k + 1)) happ))) ?_
  exact exteriorPowerStalkEquiv_germ_homogeneousProd A gen hA (k + 1) x U hx s

include gen hA in
/-- **The multiplication `⋀^k ⊗ ⋀^1 ⟶ ⋀^{k+1}` of an exterior algebra is an epimorphism.** -/
theorem epi_mulSheaf_one_right (k : ℕ) : Epi (mulSheaf A (k : ℤ) 1) := by
  refine (epi_iff_surjective_stalkMapL (mulSheaf A (k : ℤ) 1)).2 fun x => ?_
  have key : Function.Surjective
      ((exteriorPowerStalkEquiv A gen hA (k + 1) x).toLinearMap.comp
        (PresheafOfModules.stalkMapL x (valHom (mulSheaf A (k : ℤ) 1)))) := by
    rw [← LinearMap.range_eq_top]
    refine top_le_iff.1 ?_
    rw [← exteriorPower.ιMulti_span ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x), Submodule.span_le]
    rintro y ⟨v, rfl⟩
    refine (exists_common_germ M.val.presheaf x (k + 1) v).elim fun U hU =>
      hU.elim fun hx hU' => hU'.elim fun s hs => ?_
    have hv : v = fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := (funext hs).symm
    subst hv
    exact ⟨_, exteriorPowerStalkEquiv_stalkMapL_mulSheaf_ιMulti A gen hA k x U hx s⟩
  intro w
  obtain ⟨z, hz⟩ := key (exteriorPowerStalkEquiv A gen hA (k + 1) x w)
  exact ⟨z, (exteriorPowerStalkEquiv A gen hA (k + 1) x).injective hz⟩

end SheafOfModules.GradedAlgebra

namespace SheafOfModules

open MonoidalCategory

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)
  (iF : F ⟶ H) (iG : G ⟶ H)

/-- The monoidal structure of [Stacks, Tag 01CA] on sheaves of modules over the sheaf of rings
underlying a sheaf of commutative rings on a space, named here so that the notation `⊗`, `◁`,
`▷` and `α_` below refers to it. It is `Stacks.TensorSheafWorld.monoidalCategory`; naming it
once is what keeps instance search from re-deriving the three sheafification instances the
latter takes at every occurrence. -/
@[instance_reducible]
local instance monoidalSheaves :
    MonoidalCategory
      (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  Stacks.TensorSheafWorld.monoidalCategory Osharp

/-! Sheaves of modules over the ring sheaf underlying `Osharp` form an abelian category, which
is what gives the images and the lattice of subobjects the filtration below is built from. The
instance is pinned rather than restated: finding it from `SheafOfModules.instAbelian` at these
binders exceeds the default instance-synthesis budget, and
`Stacks.SheafOfModules.abelianOfSmallSite` is that instance with the budget already spent. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-! ### The wedge-product morphism on local sections, and the associativity square -/

/-- **The wedge-product component morphism on a pure tensor of two arbitrary local sections**:
the two sections are carried into the exterior algebra of `H` and multiplied there. The second
factor is untouched because the morphism `iG` of `SheafOfModules.prodWedgeHom` is here the
identity of `H`, whose induced map on exterior powers is the identity.

`SheafOfModules.prodWedgeHom_tensorSheafUnit` is the same formula on a pure tensor of two
*wedges of degree-one sections*, where both factors are rewritten as one ordered product; this
one keeps the two factors abstract, which is what the associativity computation below needs. -/
theorem prodWedgeHomIdRight_val_app_tensorSheafUnit (p q : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (a : (AF.exteriorPower p).val.obj U) (b : (A.exteriorPower q).val.obj U) :
    (prodWedgeHom AF A A iF (𝟙 H) p q).val.app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower p) (A.exteriorPower q)).app U
          (a ⊗ₜ b)) =
      (A.exterior.mul (p : ℤ) (q : ℤ)).app U
        (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
          (p : ℤ)).val.app U a) b := by
  have hmap := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
    (AF.exteriorPower p) (A.exteriorPower q)
    ((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app (p : ℤ))
    ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra (𝟙 H)).app (q : ℤ)) U a b
  have hid : ((A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra
      (𝟙 H)).app (q : ℤ)).val.app U b = b := by
    have h1 : (A.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra (𝟙 H)).app (q : ℤ) =
        𝟙 (A.exterior.piece (q : ℤ)) :=
      A.exterior_isExteriorAlgebra.pieceMap_id (q : ℤ)
    rw [h1]
    rfl
  refine Eq.trans (congrArg
    (fun z => (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)).val.app U z) hmap) ?_
  refine Eq.trans (GradedAlgebra.mulSheaf_unit A.exterior (p : ℤ) (q : ℤ) U _ _) ?_
  exact congrArg (fun y => (A.exterior.mul (p : ℤ) (q : ℤ)).app U _ y) hid

/-! ### The wedge-product morphism through the second structural map -/

/-- The tensor bifunctor on a pair of morphisms is the second component followed by the first. -/
private theorem sheafTensor_map_eq_id_comp {A₁ A₂ B₁ B₂ : SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((f, g) : (A₁, B₁) ⟶ (A₂, B₂)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((𝟙 A₁, g) : (A₁, B₁) ⟶ (A₁, B₂)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((f, 𝟙 B₂) : (A₁, B₂) ⟶ (A₂, B₂)) :=
  Eq.trans (congrArg _ (Prod.ext (Category.id_comp f).symm (Category.comp_id g).symm))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map_comp _ _)

/-- The tensor bifunctor on a pair of morphisms is the first component followed by the second. -/
private theorem sheafTensor_map_eq_comp_id {A₁ A₂ B₁ B₂ : SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((f, g) : (A₁, B₁) ⟶ (A₂, B₂)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((f, 𝟙 B₁) : (A₁, B₁) ⟶ (A₂, B₁)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((𝟙 A₂, g) : (A₂, B₁) ⟶ (A₂, B₂)) :=
  Eq.trans (congrArg _ (Prod.ext (Category.comp_id f).symm (Category.id_comp g).symm))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map_comp _ _)


/-- **The wedge-product morphism out of `⋀^pF ⊗ ⋀^qG` is the one out of `⋀^pF ⊗ ⋀^qH`,
precomposed with `⋀^q` of the second structural map**, in the spelling of the tensor-product
bifunctor. Both are `⋀^p(iF) ⊗ ⋀^q(iG)` followed by the multiplication of the exterior algebra of
`H`, read with the second factor split off; the map on exterior powers induced by `𝟙 H` is the
identity. -/
theorem prodWedgeHom_eq_tensorSheafBifunctor_map_comp (p q : ℕ) :
    prodWedgeHom AF AG A iF iG p q =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((𝟙 (AF.exteriorPower p),
              AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) :
            (AF.exteriorPower p, AG.exteriorPower q) ⟶
              (AF.exteriorPower p, A.exteriorPower q)) ≫
        prodWedgeHom AF A A iF (𝟙 H) p q := by
  -- Neither `rw [← Category.assoc]` nor `rw [hpair]` can fire after unfolding `prodWedgeHom`:
  -- the unfolded body spells the tensor bifunctor in the two-step form, which is not
  -- type-correct at `implicit` transparency, while `hpair` is stated at the uncurried spelling.
  -- Both sides are reached as terms instead, which elaborate at default transparency.
  refine Eq.trans ?_ (congrArg (fun z =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((𝟙 (AF.exteriorPower p),
              AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) :
            (AF.exteriorPower p, AG.exteriorPower q) ⟶
              (AF.exteriorPower p, A.exteriorPower q)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
            ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ), z) :
              (AF.exteriorPower p, A.exteriorPower q) ⟶ (A.exteriorPower p, A.exteriorPower q)) ≫
          GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)))
    (A.exterior_isExteriorAlgebra.pieceMap_id (q : ℤ)).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact congrArg (fun z => z ≫ GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ))
    (sheafTensor_map_eq_id_comp _ _)

/-- `SheafOfModules.prodWedgeHom_eq_tensorSheafBifunctor_map_comp` in the left-whiskering
spelling of the monoidal structure of [Stacks, Tag 01CA], which is the one the statements about
the wedge filtration are written in. -/
theorem prodWedgeHom_eq_whiskerLeft_pieceMap_comp (p q : ℕ) :
    prodWedgeHom AF AG A iF iG p q =
      (AF.exteriorPower p ◁
          AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) ≫
        prodWedgeHom AF A A iF (𝟙 H) p q :=
  (prodWedgeHom_eq_tensorSheafBifunctor_map_comp AF AG A iF iG p q).trans
    (congrArg (fun z : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Osharp)).obj (AF.exteriorPower p, AG.exteriorPower q) ⟶
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower p, A.exteriorPower q) =>
        z ≫ prodWedgeHom AF A A iF (𝟙 H) p q)
      (Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
        (AF.exteriorPower p)
        (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ))).symm)

/-! ### The associativity square -/

/-- **Peeling a factor of `F` off the left-hand side of the wedge-product component
morphism.** The composite

`(⋀^k F ⊗ ⋀^j F) ⊗ ⋀^p H ⟶ ⋀^{k+j} F ⊗ ⋀^p H ⟶ ⋀^{k+j+p} H`,

whose first map multiplies the two factors of `F` inside the exterior algebra of `F`, agrees
with the composite which instead multiplies the `⋀^j F` factor into `⋀^p H` first:

`(⋀^k F ⊗ ⋀^j F) ⊗ ⋀^p H ≅ ⋀^k F ⊗ (⋀^j F ⊗ ⋀^p H) ⟶ ⋀^k F ⊗ ⋀^{j+p} H ⟶ ⋀^{k+j+p} H`.

Both are the triple product `iF a ∧ iF b ∧ c` taken in the exterior algebra of `H`, so the
content is the associativity of that algebra together with the fact that the comparison
homomorphism `⋀ F ⟶ ⋀ H` induced by `iF` preserves products. -/
theorem mulSheafTensorId_comp_prodWedgeHom_id (k j p : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (A.exteriorPower p)) :
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
            A.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫
        prodWedgeHom AF A A iF (𝟙 H) (k + j) p =
      (α_ (AF.exteriorPower k) (AF.exteriorPower j) (A.exteriorPower p)).hom ≫
        AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) j p ≫
          prodWedgeHom AF A A iF (𝟙 H) k (j + p) ≫
            eqToHom (congrArg A.exterior.piece
              (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm) := by
  have hO := Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp
  refine PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Osharp)
    (F := AF.exteriorPower k) (G := AF.exteriorPower j) (H := A.exteriorPower p)
    (Q := A.exterior.piece ((k : ℤ) + (j : ℤ) + (p : ℤ))) fun U x y z => ?_
  have hL : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (A.exteriorPower p)) :
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
              A.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫
        prodWedgeHom AF A A iF (𝟙 H) (k + j) p).val.app U
      ((PresheafOfModules.tensorSheafUnit
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j))
          (A.exteriorPower p)).app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k) (AF.exteriorPower j)).app U
          (x ⊗ₜ y) ⊗ₜ z)) =
      (A.exterior.mul ((k : ℤ) + (j : ℤ)) (p : ℤ)).app U
        (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
          ((k : ℤ) + (j : ℤ))).val.app U ((AF.exterior.mul (k : ℤ) (j : ℤ)).app U x y)) z :=
    (congrArg ((prodWedgeHom AF A A iF (𝟙 H) (k + j) p).val.app U)
        ((Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j))
            (A.exteriorPower p) (GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ))
            (𝟙 (A.exteriorPower p)) U
            ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k)
              (AF.exteriorPower j)).app U (x ⊗ₜ y)) z).trans
          (congrArg (fun t => (PresheafOfModules.tensorSheafUnit
              (AF.exteriorPower (k + j)) (A.exteriorPower p)).app U (t ⊗ₜ z))
            (GradedAlgebra.mulSheaf_unit AF.exterior (k : ℤ) (j : ℤ) U x y)))).trans
      (prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF (k + j) p U _ z)
  have h1 := Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp hO
    (AF.exteriorPower k) (AF.exteriorPower j) (A.exteriorPower p) U x y z
  have h2 := Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
    (AF.exteriorPower k) (prodWedgeHom AF A A iF (𝟙 H) j p) x
    ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower j) (A.exteriorPower p)).app U (y ⊗ₜ z))
  have h3 := prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF j p U y z
  have h4 := prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF k (j + p) U x
    ((A.exterior.mul (j : ℤ) (p : ℤ)).app U
      (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
        (j : ℤ)).val.app U y) z)
  have hmulmul := (AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).map_mul
    (k : ℤ) (j : ℤ) U x y
  have hassoc : (A.exterior.mul ((k : ℤ) + (j : ℤ)) (p : ℤ)).app U
        ((A.exterior.mul (k : ℤ) (j : ℤ)).app U
          (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
            (k : ℤ)).val.app U x)
          (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
            (j : ℤ)).val.app U y)) z =
      (eqToHom (congrArg A.exterior.piece
          (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm)).val.app U
        ((A.exterior.mul (k : ℤ) ((j : ℤ) + (p : ℤ))).app U
          (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
            (k : ℤ)).val.app U x)
          ((A.exterior.mul (j : ℤ) (p : ℤ)).app U
            (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
              (j : ℤ)).val.app U y) z)) :=
    eq_of_heq ((A.exterior.mul_assoc (k : ℤ) (j : ℤ) (p : ℤ) U _ _ z).trans
      (Stacks.TensorSheafWorld.heq_eqToHom_val_app A.exterior.piece
        (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm U _).symm)
  refine hL.trans ((congrArg (fun t => (A.exterior.mul ((k : ℤ) + (j : ℤ)) (p : ℤ)).app U t z)
    hmulmul).trans (hassoc.trans ?_))
  refine congrArg ((eqToHom (congrArg A.exterior.piece
    (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm)).val.app U) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun w => (prodWedgeHom AF A A iF (𝟙 H) k (j + p)).val.app U
      ((AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) j p).val.app U w)) h1) ?_)
  refine Eq.trans (congrArg ((prodWedgeHom AF A A iF (𝟙 H) k (j + p)).val.app U)
    (h2.trans (congrArg (fun t => (PresheafOfModules.tensorSheafUnit (AF.exteriorPower k)
      (A.exteriorPower (j + p))).app U (x ⊗ₜ t)) h3))) h4

/-- `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom` at a degree-one factor of `F`, which is
the shape the step-by-one containment of the wedge filtration consumes: there the factor that is
multiplied in is `⋀^1 F`, because the multiplication `⋀^k F ⊗ ⋀^1 F ⟶ ⋀^{k+1} F` is the one known
to be an epimorphism. -/
theorem mulSheafTensorId_comp_prodWedgeHom_one (k p : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) 1, 𝟙 (A.exteriorPower p)) :
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower k, AF.exteriorPower 1),
            A.exteriorPower p) ⟶ (AF.exteriorPower (k + 1), A.exteriorPower p)) ≫
        prodWedgeHom AF A A iF (𝟙 H) (k + 1) p =
      (α_ (AF.exteriorPower k) (AF.exteriorPower 1) (A.exteriorPower p)).hom ≫
        AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 p ≫
          prodWedgeHom AF A A iF (𝟙 H) k (1 + p) ≫
            eqToHom (congrArg A.exterior.piece
              (add_assoc (k : ℤ) (1 : ℤ) (p : ℤ)).symm) :=
  mulSheafTensorId_comp_prodWedgeHom_id AF A iF k 1 p

/-- **Moving the second structural map out of the wedge of the two `F`-factors.** Multiplying
the two factors of `F` together and then wedging the result against `⋀^pG` is the same as
carrying `⋀^pG` into `⋀^pH` first: the two differ only by the bifunctoriality of the tensor
product, `SheafOfModules.prodWedgeHom_eq_tensorSheafBifunctor_map_comp` splitting off the second
structural map. -/
theorem mulSheafTensorId_comp_prodWedgeHom_eq_mulSheafTensorPieceMap (k j p : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (AG.exteriorPower p)) :
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
            AG.exteriorPower p) ⟶ (AF.exteriorPower (k + j), AG.exteriorPower p)) ≫
        prodWedgeHom AF AG A iF iG (k + j) p =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ),
              AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ)) :
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
              AG.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫
        prodWedgeHom AF A A iF (𝟙 H) (k + j) p := by
  -- `← Category.assoc` is applied as a term: the goal mentions the tensor bifunctor at the
  -- uncurried spelling, which is not type-correct at the `implicit` transparency `rw` matches at.
  refine Eq.trans (congrArg (fun z =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (AG.exteriorPower p)) :
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
              AG.exteriorPower p) ⟶ (AF.exteriorPower (k + j), AG.exteriorPower p)) ≫ z)
    (prodWedgeHom_eq_tensorSheafBifunctor_map_comp AF AG A iF iG (k + j) p)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫ prodWedgeHom AF A A iF (𝟙 H) (k + j) p)
    (sheafTensor_map_eq_comp_id _ _).symm

/-- **Splitting the pair `(mulSheaf, ⋀^p(iG))` into its two one-variable parts.** The
bifunctoriality of the tensor product, in the order that puts the second structural map first;
this is what lets the case `iG = 𝟙 H` of the associativity square be applied to the second
factor. The tail `c` is carried along so that the step applies where that square has already
been expanded. -/
theorem mulSheafTensorPieceMap_eq_pieceMapRight_comp_mulSheafTensorId (k j p : ℕ)
    {W : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (c : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Osharp)).obj (AF.exteriorPower (k + j), A.exteriorPower p) ⟶ W) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ),
              AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ)) :
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
              AG.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫ c =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
            ((𝟙 ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j)),
                AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ)) :
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
                AG.exteriorPower p) ⟶
                  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                      Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
                    A.exteriorPower p)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
            ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (A.exteriorPower p)) :
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
                A.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫ c := by
  exact (congrArg (fun z => z ≫ c) (sheafTensor_map_eq_id_comp _ _)).trans (Category.assoc _ _ _)

/-- **The interchange of the two whiskerings across the associator.** Whiskering by `⋀^p(iG)`
against the wedge of the two `F`-factors and then regrouping is the same as regrouping first and
whiskering `⋀^p(iG)` into the inner wedge-product morphism: the first step is the naturality of
the associator in its last variable
(`CategoryTheory.MonoidalCategory.associator_naturality_right`), the second is
`SheafOfModules.prodWedgeHom_eq_whiskerLeft_pieceMap_comp`. This is the step the associativity
square was missing, and the one the graded piece of [Stacks, Section 0FMK] needs: it is what lets
a factor of `F` be moved across while the second structural map is a section of the quotient
rather than the identity. The tail `c` is carried along so that the step applies where the
associativity square has already been expanded. -/
theorem whiskerLeft_pieceMap_comp_associator_hom_comp (k j p : ℕ)
    {W : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (c : AF.exteriorPower k ⊗ A.exteriorPower (j + p) ⟶ W) :
    ((AF.exteriorPower k ⊗ AF.exteriorPower j) ◁
          AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ)) ≫
        (α_ (AF.exteriorPower k) (AF.exteriorPower j) (A.exteriorPower p)).hom ≫
          (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) j p) ≫ c =
      (α_ (AF.exteriorPower k) (AF.exteriorPower j) (AG.exteriorPower p)).hom ≫
        (AF.exteriorPower k ◁ prodWedgeHom AF AG A iF iG j p) ≫ c := by
  rw [MonoidalCategory.associator_naturality_right_assoc,
    ← Category.assoc (AF.exteriorPower k ◁ AF.exteriorPower j ◁
      AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ))]
  refine congrArg (fun z => (α_ (AF.exteriorPower k) (AF.exteriorPower j)
      (AG.exteriorPower p)).hom ≫ z ≫ c) ?_
  refine Eq.trans (MonoidalCategory.whiskerLeft_comp (AF.exteriorPower k)
    (AF.exteriorPower j ◁
      AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ))
    (prodWedgeHom AF A A iF (𝟙 H) j p)).symm ?_
  exact congrArg (fun z => AF.exteriorPower k ◁ z)
    (prodWedgeHom_eq_whiskerLeft_pieceMap_comp AF AG A iF iG j p).symm

/-- **The associativity square at an arbitrary second structural map.** For `iF : F ⟶ H` and
`iG : G ⟶ H` the composite

`(⋀^k F ⊗ ⋀^j F) ⊗ ⋀^p G ⟶ ⋀^{k+j} F ⊗ ⋀^p G ⟶ ⋀^{k+j+p} H`,

whose first map multiplies the two factors of `F` inside the exterior algebra of `F`, agrees with
the composite which instead wedges the `⋀^j F` factor into `⋀^p G` first:

`(⋀^k F ⊗ ⋀^j F) ⊗ ⋀^p G ≅ ⋀^k F ⊗ (⋀^j F ⊗ ⋀^p G) ⟶ ⋀^k F ⊗ ⋀^{j+p} H ⟶ ⋀^{k+j+p} H`.

Note that the outer wedge of the second composite has `𝟙 H` as its second structural morphism:
after the inner wedge the second factor already lives in the exterior algebra of `H`.

This is `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_id` — the case `iG = 𝟙 H`, where the
content is the associativity of the exterior algebra of `H` on local sections — together with the
three formal steps that move `⋀^p(iG)` from the outside of the square to the inside of its second
leg. It is split that way because the case `iG = 𝟙 H` already takes 95% of the default heartbeat
budget in one declaration. -/
theorem mulSheafTensorId_comp_prodWedgeHom (k j p : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (AG.exteriorPower p)) :
          (AF.exteriorPower k ⊗ AF.exteriorPower j, AG.exteriorPower p) ⟶
            (AF.exteriorPower (k + j), AG.exteriorPower p)) ≫
        prodWedgeHom AF AG A iF iG (k + j) p =
      (α_ (AF.exteriorPower k) (AF.exteriorPower j) (AG.exteriorPower p)).hom ≫
        AF.exteriorPower k ◁ prodWedgeHom AF AG A iF iG j p ≫
          prodWedgeHom AF A A iF (𝟙 H) k (j + p) ≫
            eqToHom (congrArg A.exterior.piece
              (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm) := by
  refine Eq.trans (mulSheafTensorId_comp_prodWedgeHom_eq_mulSheafTensorPieceMap
    AF AG A iF iG k j p) ?_
  refine Eq.trans (mulSheafTensorPieceMap_eq_pieceMapRight_comp_mulSheafTensorId AF AG A iG k j p
    (prodWedgeHom AF A A iF (𝟙 H) (k + j) p)) ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) (j : ℤ), 𝟙 (A.exteriorPower p)) :
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j),
              A.exteriorPower p) ⟶ (AF.exteriorPower (k + j), A.exteriorPower p)) ≫
        prodWedgeHom AF A A iF (𝟙 H) (k + j) p)
    (Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j))
      (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ))).symm) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF.exteriorPower k, AF.exteriorPower j) ◁
        AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (p : ℤ)) ≫ z)
    (mulSheafTensorId_comp_prodWedgeHom_id AF A iF k j p)) ?_
  exact whiskerLeft_pieceMap_comp_associator_hom_comp AF AG A iF iG k j p
    (prodWedgeHom AF A A iF (𝟙 H) k (j + p) ≫
      eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (j : ℤ) (p : ℤ)).symm))

/-- **Tensoring the multiplication `⋀^k F ⊗ ⋀^1 F ⟶ ⋀^{k+1} F` with `⋀^p H` keeps it an
epimorphism**: the multiplication is one by
`SheafOfModules.GradedAlgebra.epi_mulSheaf_one_right`, and the tensor product of sheaves of
modules is right exact. -/
theorem epi_mulSheafTensorId (k p : ℕ) :
    Epi ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
      ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) 1, 𝟙 (A.exteriorPower p)) :
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            Osharp)).obj (AF.exteriorPower k, AF.exteriorPower 1),
          A.exteriorPower p) ⟶ (AF.exteriorPower (k + 1), A.exteriorPower p))) := by
  have hmul : Epi (GradedAlgebra.mulSheaf AF.exterior (k : ℤ) 1) :=
    GradedAlgebra.epi_mulSheaf_one_right AF.exterior AF.exteriorGenerator
      AF.exterior_isExteriorAlgebra k
  have hid : Epi (𝟙 (A.exteriorPower p)) := inferInstance
  exact @Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map _ _
    (Opens.grothendieckTopology ↥X) _ _ _ Osharp _ _ _ _
    (GradedAlgebra.mulSheaf AF.exterior (k : ℤ) 1) (𝟙 (A.exteriorPower p)) hmul hid

/-- **The image of the wedge-product morphism out of `⋀^{k+1} F ⊗ ⋀^p H` is contained in the
image of the one out of `⋀^k F ⊗ ⋀^{1+p} H`.** Both are subobjects of `⋀^{k+1+p} H`. The
containment is `SheafOfModules.mulSheafTensorId_comp_prodWedgeHom_one` read on images: the first
morphism, precomposed with the epimorphism which multiplies two factors of `F` together,
factors through the second. -/
theorem imageSubobject_prodWedgeHom_succ_le (k p : ℕ) :
    imageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) p) ≤
      imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + p) ≫
        eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (p : ℤ)).symm)) := by
  rw [← Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.mulSheaf AF.exterior (k : ℤ) 1, 𝟙 (A.exteriorPower p)) :
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Osharp)).obj (AF.exteriorPower k, AF.exteriorPower 1),
            A.exteriorPower p) ⟶ (AF.exteriorPower (k + 1), A.exteriorPower p)))
      (epi_mulSheafTensorId AF A k p) (prodWedgeHom AF A A iF (𝟙 H) (k + 1) p),
    mulSheafTensorId_comp_prodWedgeHom_one]
  have hmid : imageSubobject ((AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 p) ≫
        prodWedgeHom AF A A iF (𝟙 H) k (1 + p) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (p : ℤ)).symm)) ≤
      imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + p) ≫
        eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (p : ℤ)).symm)) :=
    imageSubobject_comp_le (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 p) _
  exact le_trans (imageSubobject_comp_le
    (α_ (AF.exteriorPower k) (AF.exteriorPower 1) (A.exteriorPower p)).hom _) hmid

/-- `SheafOfModules.imageSubobject_prodWedgeHom_succ_le` with the two exterior degrees of the
second factor and the total degree named by hypotheses, which is the form the filtration below
consumes. -/
theorem imageSubobject_prodWedgeHomOfEq_succ_le (k p q n : ℕ) (hq : 1 + p = q)
    (h1 : k + 1 + p = n) (h2 : k + q = n) :
    imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) (k + 1) p n h1) ≤
      imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k q n h2) := by
  subst hq
  subst h1
  rw [prodWedgeHomOfEq_rfl]
  exact imageSubobject_prodWedgeHom_succ_le AF A iF k p

/-! ### The degree-zero step -/

/-- **The degree-zero wedge-product morphism is the left unitor.** Precomposing
`⋀^0 F ⊗ ⋀ⁿ H ⟶ ⋀ⁿ H` with the global unit of the exterior algebra of `F` in the first factor
gives the action of a scalar on a local section, because the comparison homomorphism
`⋀ F ⟶ ⋀ H` carries the unit to the unit and the unit of a graded algebra acts trivially. -/
theorem oneTensorId_comp_prodWedgeHom (n : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((GradedAlgebra.oneHom AF.exterior, 𝟙 (A.exteriorPower n)) :
          (𝟙_ (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)),
            A.exteriorPower n) ⟶ (AF.exteriorPower 0, A.exteriorPower n)) ≫
        prodWedgeHom AF A A iF (𝟙 H) 0 n =
      (λ_ (A.exteriorPower n)).hom ≫
        eqToHom (congrArg A.exterior.piece (zero_add (n : ℤ)).symm) := by
  have hO := Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := 𝟙_ (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)))
    (G := A.exteriorPower n) fun U r b => ?_
  have e3 : ((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
        0).val.app U ((GradedAlgebra.oneHom AF.exterior).val.app U r) =
      (GradedAlgebra.oneHom A.exterior).val.app U r := by
    refine Eq.trans (congrArg (((AF.exterior_isExteriorAlgebra.map
        A.exterior_isExteriorAlgebra iF).app 0).val.app U)
      (GradedAlgebra.oneHom_val_app AF.exterior U r)) ?_
    refine Eq.trans ((((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
      0).val.app U).hom.map_smul r (AF.exterior.one.eval U)) ?_
    rw [(AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).map_one U]
    exact (GradedAlgebra.oneHom_val_app A.exterior U r).symm
  refine Eq.trans (congrArg ((prodWedgeHom AF A A iF (𝟙 H) 0 n).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
      (𝟙_ (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)))
      (A.exteriorPower n) (GradedAlgebra.oneHom AF.exterior)
      (𝟙 (A.exteriorPower n)) U r b)) ?_
  refine Eq.trans (prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF 0 n U
    ((GradedAlgebra.oneHom AF.exterior).val.app U r) b) ?_
  refine Eq.trans (congrArg (fun t => (A.exterior.mul (0 : ℤ) (n : ℤ)).app U t b) e3) ?_
  refine Eq.trans (GradedAlgebra.mul_oneHom_left A.exterior (n : ℤ) U r b) ?_
  exact congrArg ((eqToHom (congrArg A.exterior.piece (zero_add (n : ℤ)).symm)).val.app U)
    (Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Osharp hO
      (A.exteriorPower n) U r b).symm

/-- **The degree-zero wedge-product morphism `⋀^0 F ⊗ ⋀ⁿ H ⟶ ⋀ⁿ H` is an epimorphism**: by
`SheafOfModules.oneTensorId_comp_prodWedgeHom` it has an isomorphism as a composite with a
morphism on the left. -/
theorem epi_prodWedgeHom_zero_left (n : ℕ) : Epi (prodWedgeHom AF A A iF (𝟙 H) 0 n) := by
  have : Epi ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
      ((GradedAlgebra.oneHom AF.exterior, 𝟙 (A.exteriorPower n)) :
        (𝟙_ (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)),
          A.exteriorPower n) ⟶ (AF.exteriorPower 0, A.exteriorPower n)) ≫
      prodWedgeHom AF A A iF (𝟙 H) 0 n) := by
    rw [oneTensorId_comp_prodWedgeHom AF A iF n]
    exact @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (λ_ (A.exteriorPower n) ≪≫
      eqToIso (congrArg A.exterior.piece (zero_add (n : ℤ)).symm)))
  exact epi_of_epi ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
      ((GradedAlgebra.oneHom AF.exterior, 𝟙 (A.exteriorPower n)) :
        (𝟙_ (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)),
          A.exteriorPower n) ⟶ (AF.exteriorPower 0, A.exteriorPower n)))
    (prodWedgeHom AF A A iF (𝟙 H) 0 n)

/-! ### The filtration of an exterior power -/

/-- **The filtration of `⋀ⁿ H` attached to a morphism `iF : F ⟶ H`**: its `k`-th step is the
image of the wedge-product morphism

`⋀^k F ⊗ ⋀^{n-k} H ⟶ ⋀ⁿ H`,

and it is `⊥` for `k > n`. For the morphism `f^*Ω_{Y/S} ⟶ Ω_{X/S}` of the differentials sequence
of a smooth morphism this is the filtration of the sheaf `Ω^n_{X/S}` of [Stacks, Section 0FMK]
whose graded pieces that section identifies. -/
def exteriorImageFiltration (n k : ℕ) : Subobject (A.exteriorPower n) :=
  if h : k ≤ n then
    imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k (n - k) n (Nat.add_sub_cancel' h))
  else ⊥

/-- Below the top degree the step of the filtration is the image of the wedge-product
morphism. -/
theorem exteriorImageFiltration_of_le (n k : ℕ) (h : k ≤ n) :
    exteriorImageFiltration AF A iF n k =
      imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k (n - k) n (Nat.add_sub_cancel' h)) :=
  dite_eq_left h

/-- **The filtration of `⋀ⁿ H` vanishes above `n`**: there is no wedge of more than `n` sections
of `F` inside `⋀ⁿ H`. -/
theorem exteriorImageFiltration_eq_bot (n k : ℕ) (h : n < k) :
    exteriorImageFiltration AF A iF n k = ⊥ :=
  dite_eq_right (by omega)

/-- **The filtration of `⋀ⁿ H` decreases by one step.** -/
theorem exteriorImageFiltration_succ_le (n k : ℕ) :
    exteriorImageFiltration AF A iF n (k + 1) ≤ exteriorImageFiltration AF A iF n k := by
  by_cases hk : k + 1 ≤ n
  · rw [exteriorImageFiltration_of_le AF A iF n (k + 1) hk,
      exteriorImageFiltration_of_le AF A iF n k (by omega)]
    exact imageSubobject_prodWedgeHomOfEq_succ_le AF A iF k (n - (k + 1)) (n - k) n (by omega)
      (Nat.add_sub_cancel' hk) (Nat.add_sub_cancel' (by omega))
  · rw [exteriorImageFiltration_eq_bot AF A iF n (k + 1) (by omega)]
    exact bot_le

/-- **The filtration of `⋀ⁿ H` is decreasing.** -/
theorem exteriorImageFiltration_antitone (n : ℕ) :
    Antitone (exteriorImageFiltration AF A iF n) :=
  antitone_nat_of_succ_le (exteriorImageFiltration_succ_le AF A iF n)

/-- **The degree-zero wedge-product morphism, transported along `0 + q = n`, is an
epimorphism.** -/
theorem epi_prodWedgeHomOfEq_zero_left (q n : ℕ) (h : 0 + q = n) :
    Epi (prodWedgeHomOfEq AF A A iF (𝟙 H) 0 q n h) := by
  subst h
  rw [prodWedgeHomOfEq_rfl]
  exact epi_prodWedgeHom_zero_left AF A iF q

/-- **The filtration of `⋀ⁿ H` is exhaustive**: its zeroth step is all of `⋀ⁿ H`, because the
degree-zero wedge-product morphism `⋀^0 F ⊗ ⋀ⁿ H ⟶ ⋀ⁿ H` is an epimorphism. -/
theorem exteriorImageFiltration_zero (n : ℕ) : exteriorImageFiltration AF A iF n 0 = ⊤ := by
  rw [exteriorImageFiltration_of_le AF A iF n 0 (Nat.zero_le n)]
  exact @Subobject.imageSubobject_eq_top_of_epi _ _ _ _ _ _ _
    (epi_prodWedgeHomOfEq_zero_left AF A iF (n - 0) n (Nat.add_sub_cancel' (Nat.zero_le n)))

end SheafOfModules

/-! ### The filtration of the relative forms of a morphism of schemes -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- **The filtration of `Ω^n_{X/S}` by the forms pulled back from `Y`.** For `f : X ⟶ Y` over a
base `S` the transitivity sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` induces on
`Ω^n_{X/S} = ⋀^nΩ_{X/S}` the filtration whose `k`-th step is the image of

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^{n-k}Ω_{X/S} ⟶ ⋀^nΩ_{X/S}`.

This is the filtration of the single sheaf `Ω^n_{X/S}` whose graded pieces
[Stacks, Section 0FMK] identifies. -/
noncomputable abbrev relativeDifferentialsExteriorFiltration (f : X ⟶ Y) (g : Y ⟶ S) (n k : ℕ) :
    Subobject ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₂).exteriorPower n) :=
  _root_.SheafOfModules.exteriorImageFiltration
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₂)
    (relativeDifferentialsShortComplex f g).f n k

/-- **The filtration of the exterior powers of the relative differentials is decreasing and
exhaustive.** Its zeroth step is all of `Ω^n_{X/S}` and its steps decrease. This is the first
step of the identification of the graded pieces of [Stacks, Section 0FMK]: the filtration on the
single sheaf `Ω^n_{X/S}` whose successive quotients that section computes.

The remaining clause, that the steps above `n` are zero, is
`SheafOfModules.exteriorImageFiltration_eq_bot`, which applies to this instance verbatim; it is
not folded into the conjunction here only because writing `⊥` for this lattice of subobjects
makes instance search for its bottom element exceed the default budget, while the generic
statement is proved at binders where the abelian structure is named. -/
theorem relativeDifferentialsExteriorFiltration_spec (f : X ⟶ Y) (g : Y ⟶ S) (n : ℕ) :
    relativeDifferentialsExteriorFiltration f g n 0 = ⊤ ∧
      Antitone (relativeDifferentialsExteriorFiltration f g n) :=
  ⟨_root_.SheafOfModules.exteriorImageFiltration_zero _ _ _ n,
    _root_.SheafOfModules.exteriorImageFiltration_antitone _ _ _ n⟩

end AlgebraicGeometry.Scheme.Hom

end
