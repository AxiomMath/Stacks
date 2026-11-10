module

public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Modules.OpenSubspaceRestrictionTransport
public import StacksFrontier.AlgebraicGeometry.Modules.ProdWedgeOpenSubspaceAlgebras

/-!
# The graded piece of the wedge filtration, read at algebras chosen on the open subspace

Let `X` be a ringed space, `U ⊆ X` open, `F`, `H` sheaves of `𝒪_X`-modules, `iF : F ⟶ H`, and let
`AF`, `A` be bundles of tensor, exterior and symmetric algebras of `F` and `H` on `X` and `BF`,
`B` bundles of algebras of `F|_U` and `H|_U` **chosen on `U`** — arbitrary ones; nothing here
transports a bundle across restriction.

`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspace` carries the comparisons of
[Stacks, Section 0FMK] across restriction to `U` with the restricted exterior algebra `A|_U` still
on the right-hand sides, so a consumer over `U` is then still owed the reading of `A|_U` as an
exterior algebra chosen on `U`.
`StacksFrontier.AlgebraicGeometry.Modules.ProdWedgeOpenSubspaceAlgebras` pays that debt for the
**wedge-product morphism** and for the **cokernel** it has as target. This file pays it for the
**canonical morphism onto the ambient quotient of the graded piece**,
`SheafOfModules.exteriorGradedHom`:

`(⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH)|_U`  is  `⋀^k(F|_U) ⊗ ⋀^{1+m}(H|_U) ⟶ ⋀ⁿ(H|_U)/F^{k+1}`,

read through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` and the two exterior-algebra comparisons at the source and
through the cokernel identification at the target.

The splitting-free comparison of [Stacks, Section 0FMK] is not built from morphisms that cross one
at a time; it is a descent along the presentation of [Stacks, Tag 01CJ], so what crosses is its
defining equation, cancelled against the restricted surjection of that tag. Monomorphy of the
resulting quotient-level crossing over the members of an open covering then makes the comparison
an isomorphism, which is the globalization of the section.

## Main results

* `SheafOfModules.openSubspaceTensorExteriorPieceIso`: **the source identification**
  `(⋀^kF ⊗ A_n)|_U ≅ ⋀^k(F|_U) ⊗ B_n` — the tensor-product identification of
  `SheafOfModules.openSubspaceTensorBifunctorIso` followed by the tensor bifunctor applied to the
  pair of exterior-algebra comparisons. Its second factor is an arbitrary homogeneous piece, so
  one definition serves the three degrees the comparisons use.
* `SheafOfModules.map_tensorLeftFunctor_map_pieceMap_comp_openSubspaceTensorExteriorPieceIso_hom`
  and `…_map_eqToHom_comp_…`: **the map induced on a homogeneous piece, and a transport of the
  degree, tensored on the left with `⋀^kF`, cross restriction**, read through the source
  identification at each end.
* `SheafOfModules.map_eqToHom_comp_exteriorRestrictOpenSubspaceIso_hom`: **a transport of the
  degree crosses the exterior-algebra comparison.**
* `SheafOfModules.exteriorGradedCokernelOpenSubspaceIso`: **the ambient object of the restricted
  graded piece is the one of the bundles chosen on `U`** — the cokernel identification of
  `ProdWedgeOpenSubspaceAlgebras` at the wedge-product morphism of the filtration.
* `SheafOfModules.map_cokernelπ_comp_exteriorGradedCokernelOpenSubspaceIso`: the restricted
  cokernel projection, read through that identification.
* `SheafOfModules.openSubspaceRestriction_map_exteriorGradedHom_comp_cokernelIso`: **the canonical
  morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH` restricted to `U` is the one of the bundles chosen
  on `U`**, conjugated by the source identification and the cokernel identification.
* `SheafOfModules.epi_openSubspaceRestriction_map_tensorLeftFunctor_map_relComplex_g`: **the
  restricted surjection of [Stacks, Tag 01CJ], tensored on the left with `⋀^kT.X₁`, is an
  epimorphism** — the cancellation the splitting-free comparison is pinned down against.
* `SheafOfModules.openSubspaceShortComplex`: the presentation of [Stacks, Tag 01CJ] restricted to
  `U`, re-typed at the open subspace's own spelling of its sheaf of rings.
* `SheafOfModules.openSubspaceRestriction_map_exteriorGradedQuotientHom_comp_cokernelIso`: **the
  splitting-free comparison of [Stacks, Section 0FMK], read at the quotient level, crosses
  restriction to `U`** — the five squares of the two defining equations, cancelled against the
  epimorphism of [Stacks, Tag 01CJ].
* `SheafOfModules.mono_openSubspaceRestriction_map_exteriorGradedQuotientHom_of_splitting`: **the
  restricted quotient-level comparison is a monomorphism over an open on which the presentation
  of [Stacks, Tag 01CJ] splits.**
* `SheafOfModules.isIso_exteriorGradedQuotientComparison_of_mono_restrict` and
  `SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split`: **the comparison of
  [Stacks, Section 0FMK] is an isomorphism**, from monomorphy of its quotient-level form over an
  open covering and, with the previous item, from a splitting of the presentation over the
  members of one.
* `SheafOfModules.eq_of_epi_two_ladders`, `SheafOfModules.mapCompThreeLadder`,
  `SheafOfModules.mono_of_comp_iso_eq_iso_comp` and the three smaller reassociation lemmas:
  **the generic shapes the squares above are composed in.**

## Implementation notes

Two re-typings are made once here rather than left to the unifier in every statement downstream,
each of them an equality by `rfl` between two small closed terms.
`SheafOfModules.exteriorGradedCokernelOpenSubspaceIso` re-types the cokernel identification of
`ProdWedgeOpenSubspaceAlgebras` so that the second factor's identity is the identity of the
restriction, `𝟙 ((openSubspaceRestriction U).obj H)`, rather than the restriction of the identity:
comparing the two `CategoryTheory.Limits.cokernel` applications means comparing their
`HasCokernel` instance arguments as well. `SheafOfModules.openSubspaceShortComplex` re-types the
restricted presentation of [Stacks, Tag 01CJ] at the open subspace's own spelling of its sheaf of
rings, `CategoryTheory.Sheaf.toRingCat`, which is the spelling both the bundles chosen on `U` and
`SheafOfModules.exteriorGradedQuotientHom` are stated over, whereas the target category of
`SheafOfModules.openSubspaceRestriction` is spelled with
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf`. Being a
`CategoryTheory.ShortComplex.mk`, it also needs no `[Functor.PreservesZeroMorphisms]` instance,
which `CategoryTheory.ShortComplex.map` of `SheafOfModules.openSubspaceRestriction` and of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` cannot both have in one statement; a consumer
holding a splitting of the `restrictFunctor` form converts it with
`SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor`.

The bundles of algebras on `U` are hypotheses, as in `ProdWedgeOpenSubspaceAlgebras`, because that
is what keeps a bundle from having to be transported across restriction. A consumer wanting a
canonical choice has one: `Stacks.SheafOfModules.openSubspaceAlgebras U F` is
`SheafOfModules.ringedSpaceAlgebras` of the open subspace at `F|_U`, and it is accepted as a
`SheafOfModules.TensorExteriorSymmetricAlgebras` at exactly the site and sheaf of commutative
rings the statements here are written over.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
  PresheafOfModules TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)
open Stacks.SheafOfModules.PushforwardSheafification

universe u

namespace CategoryTheory.Limits

/-- **The restricted projection onto a cokernel, read through the two-step identification of the
restricted cokernel with a cokernel formed downstream**: a functor preserving the cokernel
identifies the restricted cokernel with the cokernel of the restricted morphism, and a commuting
square of isomorphisms identifies that with a cokernel formed on the other side; composed, the
image of the projection is the target isomorphism followed by the other projection. -/
theorem map_cokernelπ_comp_preservesCokernelIso_trans_cokernelMapIso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (L : C ⥤ D) [L.PreservesZeroMorphisms] {P Q : C} (f : P ⟶ Q) [HasCokernel f]
    [HasCokernel (L.map f)] [PreservesColimit (parallelPair f 0) L]
    {P' Q' : D} (f' : P' ⟶ Q') [HasCokernel f'] (p : L.obj P ≅ P') (q : L.obj Q ≅ Q')
    (w : L.map f ≫ q.hom = p.hom ≫ f') :
    L.map (cokernel.π f) ≫
        (PreservesCokernel.iso L f ≪≫ cokernel.mapIso (L.map f) f' p q w).hom =
      q.hom ≫ cokernel.π f' := by
  rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

end CategoryTheory.Limits

namespace SheafOfModules

/-! ### The generic shapes the squares are composed in -/

/-- **A ladder of three commuting squares composes**: a threefold composite postcomposed with a
morphism is the leftmost vertical followed by the other side of the ladder.

Stated at generic objects of a generic category, where the reassociation is available: at the
concrete objects of the wedge filtration `simp only [CategoryTheory.Category.assoc]` does not
fire. -/
theorem compThreeLadder {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (i : A₃ ⟶ A₄)
    (s : A₀ ⟶ B₀) (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂) (c' : B₂ ⟶ A₄)
    (β : A₁ ⟶ B₁) (γ : A₂ ⟶ B₂)
    (hc : c ≫ i = γ ≫ c') (hb : b ≫ γ = β ≫ b') (ha : a ≫ β = s ≫ a') :
    (a ≫ b ≫ c) ≫ i = s ≫ a' ≫ b' ≫ c' := by
  rw [Category.assoc, Category.assoc, hc, ← Category.assoc b γ c', hb, Category.assoc,
    ← Category.assoc a β, ha, Category.assoc]

/-- **The ladder of `SheafOfModules.compThreeLadder` read through a functor**, with the threefold
composite applied to by the functor rather than formed from its images, fusing the two
`CategoryTheory.Functor.map_comp` steps into the ladder. -/
theorem mapCompThreeLadder {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {A₄ B₀ B₁ B₂ : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (i : L.obj A₃ ⟶ A₄)
    (s : L.obj A₀ ⟶ B₀) (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂) (c' : B₂ ⟶ A₄)
    (β : L.obj A₁ ⟶ B₁) (γ : L.obj A₂ ⟶ B₂)
    (hc : L.map c ≫ i = γ ≫ c') (hb : L.map b ≫ γ = β ≫ b') (ha : L.map a ≫ β = s ≫ a') :
    L.map (a ≫ b ≫ c) ≫ i = s ≫ a' ≫ b' ≫ c' := by
  rw [L.map_comp, L.map_comp]
  exact compThreeLadder _ _ _ _ _ _ _ _ β γ hc hb ha

/-- Two factorizations of one morphism stay equal under a functor. -/
theorem mapCompEqMapComp {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {A B W A' : C} (f : A ⟶ B) (g : B ⟶ W) (f' : A ⟶ A') (g' : A' ⟶ W) (h : f ≫ g = f' ≫ g') :
    L.map f ≫ L.map g = L.map f' ≫ L.map g' := by
  rw [← L.map_comp, h, L.map_comp]

/-- **Two ladders out of a common epimorphism, joined at the far end, identify their two right
legs.** This is the shape in which a morphism characterized by a defining equation is matched
against a morphism constructed downstream: `E` is the epimorphism both defining equations are
precomposed with, `q ≫ i` and `s₃ ≫ Q` the two legs, and the five squares say that each leg
precomposed with `E` factors through a common `c`.

The epimorphy is a hypothesis rather than an instance, so that the field
`CategoryTheory.Epi.left_cancellation` can be applied to the proof term directly instead of
`CategoryTheory.cancel_epi` having to find it by instance search. -/
theorem eq_of_epi_two_ladders {C : Type*} [Category C]
    {Z C₀ C₁ W D₀ D₁ D₂ D₃ : C} {E : Z ⟶ C₀} (hE : Epi E)
    (q : C₀ ⟶ C₁) (i : C₁ ⟶ W) (s₃ : C₀ ⟶ D₀) (Q : D₀ ⟶ W)
    (a : Z ⟶ D₁) (b : D₁ ⟶ C₁) (s : D₁ ⟶ D₂) (c : D₂ ⟶ W)
    (a' : Z ⟶ D₃) (b' : D₃ ⟶ D₀) (s' : D₃ ⟶ D₂)
    (h₁ : E ≫ q = a ≫ b) (h₂ : b ≫ i = s ≫ c)
    (h₃ : E ≫ s₃ = a' ≫ b') (h₄ : b' ≫ Q = s' ≫ c)
    (h₅ : a ≫ s = a' ≫ s') :
    q ≫ i = s₃ ≫ Q := by
  refine hE.left_cancellation _ _ ?_
  rw [← Category.assoc E q i, h₁, Category.assoc a b i, h₂, ← Category.assoc a s c, h₅,
    Category.assoc a' s' c, ← h₄, ← Category.assoc a' b' Q, ← h₃, Category.assoc E s₃ Q]

/-- **A morphism conjugated by two isomorphisms into a monomorphism is a monomorphism.** This is
the shape in which a crossing of restriction to an open carries a property back: the crossing
reads `f ≫ p.hom = q.hom ≫ g` with `p` and `q` isomorphisms, so `f` is `g` conjugated, and
monomorphy passes through the isomorphism on the left and cancels off the one on the right.

Note the direction: `Stacks.AlgebraicGeometry.Modules.mono_of_comp_iso_eq` carries monomorphy
*forwards* along one isomorphism, which is not what a crossing read this way round gives. -/
theorem mono_of_comp_iso_eq_iso_comp {C : Type*} [Category C] {A B A' B' : C} {f : A ⟶ B}
    (p : B ≅ B') (q : A ≅ A') {g : A' ⟶ B'} (h : f ≫ p.hom = q.hom ≫ g) (hg : Mono g) :
    Mono f :=
  have : Mono (f ≫ p.hom) :=
    Eq.mpr (congrArg Mono h)
      (Stacks.CategoryTheory.mono_comp_of_mono _ _ (IsIso.mono_of_iso q.hom) hg)
  mono_of_mono f p.hom

/-- An identity morphism commutes past any morphism. -/
private theorem id_comp_eq_comp_id {C : Type*} [Category C] {A B : C} (f : A ⟶ B) :
    𝟙 A ≫ f = f ≫ 𝟙 B :=
  (Category.id_comp f).trans (Category.comp_id f).symm

/-! ### Two unfoldings, at the generic binders of the wedge filtration -/

section GenericUnfold

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AE : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E)

/-- **Tensoring on the left with `⋀^kE`, as it acts on a morphism**: the tensor product of the
identity of `⋀^kE` with that morphism, in the bifunctor spelling that
`SheafOfModules.openSubspaceTensorBifunctorIso_naturality` is stated at.

Named rather than left to the unifier: delta-unfolding the definition against metavariable
factors is a different problem from checking a stated equation. -/
theorem tensorLeftFunctor_map_eq_tensorSheafBifunctor_map (k : ℕ)
    {Q R : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↑X) Osharp)}
    (h : Q ⟶ R) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AE.exteriorPower k)).map h =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((𝟙 (AE.exteriorPower k), h) : (AE.exteriorPower k, Q) ⟶ (AE.exteriorPower k, R)) :=
  Stacks.CategoryTheory.obj_map_eq_uncurry_map_id _ _ _

/-- **`SheafOfModules.exteriorGradedHom` unfolded**: the wedge-product morphism onto `⋀ⁿH`, the
transport of the total degree from `k + (1 + m)` to `k + 1 + m`, and the projection onto the
quotient by the `(k+1)`-st step of the wedge filtration.

Named rather than left to the unifier, for the same reason, and stated at the generic binders so
that it serves the morphism on `X` and the morphism on the open subspace alike. -/
theorem exteriorGradedHom_eq_prodWedgeHom_comp
    {H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↑X) Osharp)}
    (AH : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↑X) H)
    (iE : E ⟶ H) (k m : ℕ) :
    exteriorGradedHom AE AH iE k m =
      prodWedgeHom AE AH AH iE (𝟙 H) k (1 + m) ≫
        eqToHom (congrArg AH.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AE AH AH iE (𝟙 H) (k + 1) m) :=
  rfl

end GenericUnfold

/-! ### The source identification, and the left-hand column of squares -/

section SourceIso

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {F N P : SheafOfModules.{u} (structureSheafRing X)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
  (AN : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) N)
  (AP : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) P)
  (BF : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj F))
  (BN : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj N))
  (BP : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj P))

/-- **The restriction of `⋀^kF ⊗ A_n` is `⋀^k(F|_U) ⊗ B_n` for bundles of algebras chosen on the
open subspace**: the identification `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` of
`SheafOfModules.openSubspaceTensorBifunctorIso`, followed by the tensor bifunctor applied to the
pair of comparisons `SheafOfModules.exteriorRestrictOpenSubspaceIso` between the restrictions of
the exterior algebras of `AF`, `AN` and the exterior algebras of `BF`, `BN`.

The second factor is an arbitrary homogeneous piece rather than an exterior power, so that one
definition serves the three degrees the comparisons of [Stacks, Section 0FMK] are read at: the
`1 + m` of the wedge filtration, and the `m + 1` of [Stacks, Tag 01CJ] at the middle and the
right-hand term of the sequence. -/
def openSubspaceTensorExteriorPieceIso (k : ℕ) (n : ℤ) :
    (openSubspaceRestriction U).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj
          (AF.exteriorPower k, AN.exterior.piece n)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).obj (BF.exteriorPower k, BN.exterior.piece n) :=
  openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (AN.exterior.piece n) ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        (restrictToOpen X U).sheaf)).mapIso
      (Iso.prod
        (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
          AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
          BF.exterior_isExteriorAlgebra (k : ℤ))
        (exteriorRestrictOpenSubspaceIso N AN.exterior AN.exteriorGenerator
          AN.exterior_isExteriorAlgebra U BN.exterior BN.exteriorGenerator
          BN.exterior_isExteriorAlgebra n))

/-- **The tensor-product identification cancels off the source identification**, leaving the
tensor bifunctor applied to the pair of exterior-algebra comparisons. This is the form in which
the source identification meets a statement whose legs are read through
`SheafOfModules.openSubspaceTensorBifunctorIso` at their source, as the crossings of
`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspace` are. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_openSubspaceTensorExteriorPieceIso_hom
    (k : ℕ) (n : ℤ) :
    (openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (AN.exterior.piece n)).inv ≫
        (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
                BF.exterior_isExteriorAlgebra (k : ℤ)).hom,
            (exteriorRestrictOpenSubspaceIso N AN.exterior AN.exteriorGenerator
                AN.exterior_isExteriorAlgebra U BN.exterior BN.exteriorGenerator
                BN.exterior_isExteriorAlgebra n).hom) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (AN.exterior.piece n)) ⟶
              (BF.exteriorPower k, BN.exterior.piece n)) :=
  Iso.inv_hom_id_assoc _ _

/-- The source identification unfolded, as a named `rfl` at a variable site rather than by the
unifier. -/
theorem openSubspaceTensorExteriorPieceIso_hom (k : ℕ) (n : ℤ) :
    (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n).hom =
      (openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (AN.exterior.piece n)).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (restrictToOpen X U).sheaf)).map
            (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                  AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
                  BF.exterior_isExteriorAlgebra (k : ℤ)).hom,
              (exteriorRestrictOpenSubspaceIso N AN.exterior AN.exteriorGenerator
                  AN.exterior_isExteriorAlgebra U BN.exterior BN.exteriorGenerator
                  BN.exterior_isExteriorAlgebra n).hom) :
              ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                  (openSubspaceRestriction U).obj (AN.exterior.piece n)) ⟶
                (BF.exteriorPower k, BN.exterior.piece n)) :=
  rfl

/-- The restriction of the identity of `⋀^kF` commutes with the comparison of the two exterior
algebras of `F|_U`, trivially: restriction carries an identity to an identity by `rfl`. This is
the first component of the pair of squares the crossings below are assembled from. -/
private theorem mapIdCommute (k : ℕ) :
    (openSubspaceRestriction U).map (𝟙 (AF.exteriorPower k)) ≫
        (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
          AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
          BF.exterior_isExteriorAlgebra (k : ℤ)).hom =
      (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
          AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
          BF.exterior_isExteriorAlgebra (k : ℤ)).hom ≫ 𝟙 (BF.exteriorPower k) :=
  id_comp_eq_comp_id _

/-- **The two squares the crossing of `⋀^kF ⊗ ⋀ⁿh` is assembled from, composed at the tensor
bifunctor**: the restricted identity of `⋀^kF` against the exterior-algebra comparison of `F|_U`,
and the restricted map induced on a homogeneous piece against the comparisons of `N|_U`, `P|_U`. -/
private theorem bifunctorMapPieceMapCompEq (h : N ⟶ P) (k : ℕ) (n : ℤ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF.exteriorPower k)),
            (openSubspaceRestriction U).map
              (AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n)) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (AN.exterior.piece n)) ⟶
              ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (AP.exterior.piece n))) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (restrictToOpen X U).sheaf)).map
            (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                  AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
                  BF.exterior_isExteriorAlgebra (k : ℤ)).hom,
              (exteriorRestrictOpenSubspaceIso P AP.exterior AP.exteriorGenerator
                  AP.exterior_isExteriorAlgebra U BP.exterior BP.exteriorGenerator
                  BP.exterior_isExteriorAlgebra n).hom) :
              ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                  (openSubspaceRestriction U).obj (AP.exterior.piece n)) ⟶
                (BF.exteriorPower k, BP.exterior.piece n)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
                BF.exterior_isExteriorAlgebra (k : ℤ)).hom,
            (exteriorRestrictOpenSubspaceIso N AN.exterior AN.exteriorGenerator
                AN.exterior_isExteriorAlgebra U BN.exterior BN.exteriorGenerator
                BN.exterior_isExteriorAlgebra n).hom) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (AN.exterior.piece n)) ⟶
              (BF.exteriorPower k, BN.exterior.piece n)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (restrictToOpen X U).sheaf)).map
            ((𝟙 (BF.exteriorPower k),
              BN.exterior_isExteriorAlgebra.pieceMap BP.exterior_isExteriorAlgebra
                ((openSubspaceRestriction U).map h) n) :
              (BF.exteriorPower k, BN.exterior.piece n) ⟶
                (BF.exteriorPower k, BP.exterior.piece n)) :=
  bifunctorMapCompMapEq
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        (restrictToOpen X U).sheaf))
    ((openSubspaceRestriction U).map (𝟙 (AF.exteriorPower k)))
    (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
      AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
      BF.exterior_isExteriorAlgebra (k : ℤ)).hom
    ((openSubspaceRestriction U).map
      (AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n))
    (exteriorRestrictOpenSubspaceIso P AP.exterior AP.exteriorGenerator
      AP.exterior_isExteriorAlgebra U BP.exterior BP.exteriorGenerator
      BP.exterior_isExteriorAlgebra n).hom
    (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
      AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
      BF.exterior_isExteriorAlgebra (k : ℤ)).hom
    (𝟙 (BF.exteriorPower k))
    (exteriorRestrictOpenSubspaceIso N AN.exterior AN.exteriorGenerator
      AN.exterior_isExteriorAlgebra U BN.exterior BN.exteriorGenerator
      BN.exterior_isExteriorAlgebra n).hom
    (BN.exterior_isExteriorAlgebra.pieceMap BP.exterior_isExteriorAlgebra
      ((openSubspaceRestriction U).map h) n)
    (mapIdCommute U AF BF k)
    (openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso U
      AN.exterior_isExteriorAlgebra AP.exterior_isExteriorAlgebra h
      BN.exterior_isExteriorAlgebra BP.exterior_isExteriorAlgebra n)

/-- **The map induced on a homogeneous piece by a morphism, tensored on the left with `⋀^kF`,
crosses restriction to an open subspace**: read through the source identification at each end, the
restriction of `⋀^kF ⊗ ⋀ⁿh` is `⋀^k(F|_U) ⊗ ⋀ⁿ(h|_U)` for the bundles chosen on `U`.

The proof is the naturality of the tensor-product identification
(`SheafOfModules.openSubspaceTensorBifunctorIso_naturality`) and then the crossing of the
functorial map on exterior powers
(`SheafOfModules.openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso`) one
tensor factor at a time, the two factors being composed by
`SheafOfModules.bifunctorMapCompMapEq`. -/
theorem map_tensorLeftFunctor_map_pieceMap_comp_openSubspaceTensorExteriorPieceIso_hom
    (h : N ⟶ P) (k : ℕ) (n : ℤ) :
    (openSubspaceRestriction U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF.exteriorPower k)).map
            (AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n)) ≫
        (openSubspaceTensorExteriorPieceIso U AF AP BF BP k n).hom =
      (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf).obj (BF.exteriorPower
            k)).map
          (BN.exterior_isExteriorAlgebra.pieceMap BP.exterior_isExteriorAlgebra
            ((openSubspaceRestriction U).map h) n) :=
  Eq.trans
    (congrArg
      (fun z => (openSubspaceRestriction U).map z ≫
        (openSubspaceTensorExteriorPieceIso U AF AP BF BP k n).hom)
      (tensorLeftFunctor_map_eq_tensorSheafBifunctor_map AF k
        (AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n)))
    (Eq.trans
      (congrArg
        (fun z => (openSubspaceRestriction U).map
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
              ((𝟙 (AF.exteriorPower k),
                AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n) :
                (AF.exteriorPower k, AN.exterior.piece n) ⟶
                  (AF.exteriorPower k, AP.exterior.piece n))) ≫ z)
        (openSubspaceTensorExteriorPieceIso_hom U AF AP BF BP k n))
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg
            (fun z => z ≫ (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                (restrictToOpen X U).sheaf)).map
                (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                      AF.exterior_isExteriorAlgebra U BF.exterior BF.exteriorGenerator
                      BF.exterior_isExteriorAlgebra (k : ℤ)).hom,
                  (exteriorRestrictOpenSubspaceIso P AP.exterior AP.exteriorGenerator
                      AP.exterior_isExteriorAlgebra U BP.exterior BP.exteriorGenerator
                      BP.exterior_isExteriorAlgebra n).hom) :
                  ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                      (openSubspaceRestriction U).obj (AP.exterior.piece n)) ⟶
                    (BF.exteriorPower k, BP.exterior.piece n)))
            (openSubspaceTensorBifunctorIso_naturality U (𝟙 (AF.exteriorPower k))
              (AN.exterior_isExteriorAlgebra.pieceMap AP.exterior_isExteriorAlgebra h n)))
          (Eq.trans (Category.assoc _ _ _)
            (Eq.trans
              (congrArg
                (fun z => (openSubspaceTensorBifunctorIso U (AF.exteriorPower k)
                  (AN.exterior.piece n)).hom ≫ z)
                (bifunctorMapPieceMapCompEq U AF AN AP BF BN BP h k n))
              (Eq.trans (Category.assoc _ _ _).symm
                (congrArg
                  (fun z => (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n).hom ≫ z)
                  (tensorLeftFunctor_map_eq_tensorSheafBifunctor_map BF k
                    (BN.exterior_isExteriorAlgebra.pieceMap BP.exterior_isExteriorAlgebra
                      ((openSubspaceRestriction U).map h) n)).symm)))))))

/-- **A transport of the degree, tensored on the left with `⋀^kF`, crosses restriction to an open
subspace.** The two degrees being equal, both transports are identities once the equality is
substituted, and restriction carries an identity to an identity by `rfl`; it is stated all the
same because the transports of [Stacks, Tag 01CJ] between the degrees `m + 1` and `1 + m` are not
identities syntactically and are what the defining equation of the splitting-free comparison
carries. -/
theorem map_tensorLeftFunctor_map_eqToHom_comp_openSubspaceTensorExteriorPieceIso_hom
    (k : ℕ) {n₁ n₂ : ℤ} (h : n₁ = n₂) :
    (openSubspaceRestriction U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF.exteriorPower k)).map
            (eqToHom (congrArg AN.exterior.piece h))) ≫
        (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n₂).hom =
      (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n₁).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf).obj (BF.exteriorPower
            k)).map
          (eqToHom (congrArg BN.exterior.piece h)) := by
  subst h
  exact Eq.trans
    (congrArg
      (fun z => (openSubspaceRestriction U).map z ≫
        (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n₁).hom)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF.exteriorPower k)).map_id
          (AN.exterior.piece n₁)))
    (Eq.trans
      (congrArg
        (fun z => z ≫ (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n₁).hom)
        ((openSubspaceRestriction U).map_id
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF.exteriorPower k)).obj
              (AN.exterior.piece n₁))))
      (Eq.trans (Category.id_comp _)
        (Eq.trans (Category.comp_id _).symm
          (congrArg
            (fun z => (openSubspaceTensorExteriorPieceIso U AF AN BF BN k n₁).hom ≫ z)
            (((Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf).obj
                (BF.exteriorPower k)).map_id
              (BN.exterior.piece n₁)).symm))))

end SourceIso

/-! ### The canonical morphism onto the ambient quotient of the graded piece -/

section GradedHomCrossing

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {F H : SheafOfModules.{u} (structureSheafRing X)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) H)
  (BF : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj F))
  (B : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj H))

/-- **A transport of the degree crosses the comparison of the two exterior algebras of `H|_U`.**
The two degrees being equal, both transports are identities once the equality is substituted. -/
theorem map_eqToHom_comp_exteriorRestrictOpenSubspaceIso_hom {n₁ n₂ : ℤ} (h : n₁ = n₂) :
    (openSubspaceRestriction U).map (eqToHom (congrArg A.exterior.piece h)) ≫
        (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
          B.exterior_isExteriorAlgebra n₂).hom =
      (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
          B.exterior_isExteriorAlgebra n₁).hom ≫
        eqToHom (congrArg B.exterior.piece h) := by
  subst h
  exact id_comp_eq_comp_id _

/-- **The ambient object of the restricted graded piece is the one of the bundles chosen on the
open subspace**: `SheafOfModules.prodWedgeHomCokernelOpenSubspaceIso` at the wedge-product
morphism of the `(k+1)`-st step of the filtration, re-typed so that the second factor's identity
is the identity of the restriction rather than the restriction of the identity.

The two are equal by `rfl`, and the re-typing is paid for once here rather than by every statement
downstream. -/
def exteriorGradedCokernelOpenSubspaceIso (iF : F ⟶ H) (p q : ℕ) :
    (openSubspaceRestriction U).obj (cokernel (prodWedgeHom AF A A iF (𝟙 H) p q)) ≅
      cokernel (prodWedgeHom BF B B ((openSubspaceRestriction U).map iF)
        (𝟙 ((openSubspaceRestriction U).obj H)) p q) :=
  prodWedgeHomCokernelOpenSubspaceIso U AF A A BF B B iF (𝟙 H) p q

/-- **The restricted projection onto `⋀ⁿH/F^{k+1}⋀ⁿH`, read through the identification of the two
ambient objects**, is the comparison of the two exterior algebras in the total degree followed by
the projection formed on the open subspace.

It is `CategoryTheory.Limits.map_cokernelπ_comp_preservesCokernelIso_trans_cokernelMapIso` at
restriction to the open subspace. -/
theorem map_cokernelπ_comp_exteriorGradedCokernelOpenSubspaceIso (iF : F ⟶ H) (p q : ℕ) :
    (openSubspaceRestriction U).map (cokernel.π (prodWedgeHom AF A A iF (𝟙 H) p q)) ≫
        (exteriorGradedCokernelOpenSubspaceIso U AF A BF B iF p q).hom =
      (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
          B.exterior_isExteriorAlgebra ((p : ℤ) + (q : ℤ))).hom ≫
        cokernel.π (prodWedgeHom BF B B ((openSubspaceRestriction U).map iF)
          (𝟙 ((openSubspaceRestriction U).obj H)) p q) :=
  map_cokernelπ_comp_preservesCokernelIso_trans_cokernelMapIso (openSubspaceRestriction U)
    (prodWedgeHom AF A A iF (𝟙 H) p q)
    (prodWedgeHom BF B B ((openSubspaceRestriction U).map iF)
      (𝟙 ((openSubspaceRestriction U).obj H)) p q)
    _ _
    (openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom U
      AF A A BF B B iF (𝟙 H) p q)

/-- **The canonical morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH` restricted to an open subspace is
the one of the bundles of algebras chosen there**, `n = k + 1 + m`: read through
`SheafOfModules.openSubspaceTensorExteriorPieceIso` at the source and through
`SheafOfModules.exteriorGradedCokernelOpenSubspaceIso` at the target, the restriction of
`SheafOfModules.exteriorGradedHom` is `SheafOfModules.exteriorGradedHom` of `BF`, `B` and the
restricted morphism. Nothing of either side then lives on `X`.

This is the reading of
`SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom` at bundles of
algebras chosen on the open subspace. The three squares it is stacked from are the
wedge-product crossing
(`SheafOfModules.openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom`
of `ProdWedgeOpenSubspaceAlgebras`), the transport of the total degree
(`SheafOfModules.map_eqToHom_comp_exteriorRestrictOpenSubspaceIso_hom`) and the cokernel
projection (`SheafOfModules.map_cokernelπ_comp_exteriorGradedCokernelOpenSubspaceIso`), composed
by `SheafOfModules.mapCompThreeLadder`. -/
theorem openSubspaceRestriction_map_exteriorGradedHom_comp_cokernelIso (iF : F ⟶ H) (k m : ℕ) :
    (openSubspaceRestriction U).map (exteriorGradedHom AF A iF k m) ≫
        (exteriorGradedCokernelOpenSubspaceIso U AF A BF B iF (k + 1) m).hom =
      (openSubspaceTensorExteriorPieceIso U AF A BF B k ((1 + m : ℕ) : ℤ)).hom ≫
        exteriorGradedHom BF B ((openSubspaceRestriction U).map iF) k m := by
  refine Eq.trans
    (congrArg
      (fun z => (openSubspaceRestriction U).map z ≫
        (exteriorGradedCokernelOpenSubspaceIso U AF A BF B iF (k + 1) m).hom)
      (exteriorGradedHom_eq_prodWedgeHom_comp AF A iF k m)) ?_
  refine Eq.trans ?_
    (congrArg
      (fun z => (openSubspaceTensorExteriorPieceIso U AF A BF B k ((1 + m : ℕ) : ℤ)).hom ≫ z)
      (exteriorGradedHom_eq_prodWedgeHom_comp BF B ((openSubspaceRestriction U).map iF) k m).symm)
  exact mapCompThreeLadder (openSubspaceRestriction U) _ _ _ _ _ _ _ _
    (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
      B.exterior_isExteriorAlgebra ((k : ℤ) + ((1 + m : ℕ) : ℤ))).hom
    (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
      B.exterior_isExteriorAlgebra (((k + 1 : ℕ) : ℤ) + ((m : ℕ) : ℤ))).hom
    (map_cokernelπ_comp_exteriorGradedCokernelOpenSubspaceIso U AF A BF B iF (k + 1) m)
    (map_eqToHom_comp_exteriorRestrictOpenSubspaceIso_hom U A B
      (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)
    (openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom U
      AF A A BF B B iF (𝟙 H) k (1 + m))

end GradedHomCrossing

/-! ### The surjection of Tag 01CJ, at the spelling the defining equation is stated in -/

section RelComplex

open Stacks.SheafOfModules.TopWedge (relComplex)

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₂)
  (BF₁ : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj T.X₁))
  (BG₃ : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj T.X₃))
  (B₂ : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj T.X₂))

/-- **The restricted surjection `⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃` of [Stacks, Tag 01CJ], tensored on
the left with `⋀^kT.X₁`, is an epimorphism.** The surjection is an epimorphism
(`SheafOfModules.epi_relComplex_g`), the tensor product of sheaves of modules carries a pair of
epimorphisms to one, and restriction to an open subspace preserves epimorphisms, being right
exact.

This is the epimorphism the *defining equation* of the splitting-free comparison is precomposed
with — tensoring on the left with `⋀^kT.X₁` applied to the surjection, as
`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom` has it. Contrast
`SheafOfModules.epi_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex`, which is the
same epimorphism at the tensor-bifunctor spelling on the open subspace and so cancels only
morphisms out of the tensor product formed there. -/
theorem epi_openSubspaceRestriction_map_tensorLeftFunctor_map_relComplex_g
    (hS : T.Exact) (hepi : Epi T.g) (k m : ℕ) :
    Epi ((openSubspaceRestriction U).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF₁.exteriorPower k)).map
          (relComplex A₂ AG₃ T.f T.g T.zero m).g)) :=
  have hrel : Epi (relComplex A₂ AG₃ T.f T.g T.zero m).g := epi_relComplex_g AG₃ A₂ hS hepi m
  have hid : Epi (𝟙 (AF₁.exteriorPower k)) := inferInstance
  have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF₁.exteriorPower k)).map
      (relComplex A₂ AG₃ T.f T.g T.zero m).g) :=
    Eq.mpr
      (congrArg Epi (tensorLeftFunctor_map_eq_tensorSheafBifunctor_map AF₁ k
        (relComplex A₂ AG₃ T.f T.g T.zero m).g))
      (@Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map _ _
        (Opens.grothendieckTopology X.carrier) _ _ _ X.sheaf _ _ _ _
        (𝟙 (AF₁.exteriorPower k)) (relComplex A₂ AG₃ T.f T.g T.zero m).g hid hrel)
  @Functor.map_epi _ _ _ _ (openSubspaceRestriction U) _ _ _ _ this

/-- **The surjection of [Stacks, Tag 01CJ], tensored on the left with `⋀^kT.X₁`, crosses
restriction to an open subspace.** This is
`SheafOfModules.map_tensorLeftFunctor_map_pieceMap_comp_openSubspaceTensorExteriorPieceIso_hom`
at the second morphism of the presentation, which is the map induced on `⋀^{m+1}` by `T.g`.

It is a separate declaration rather than an application of that lemma at the point of use because
the two spellings — the projection `.g` of the three-term complex, and the functorial map on
exterior powers — are equal only by `rfl` through a delta of
`Stacks.SheafOfModules.TopWedge.relComplex`, which is checked here between two small closed terms
rather than inside a larger statement. -/
theorem map_tensorLeftFunctor_map_relComplex_g_comp_openSubspaceTensorExteriorPieceIso_hom
    (k m : ℕ) :
    (openSubspaceRestriction U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF₁.exteriorPower k)).map
              (relComplex A₂ AG₃ T.f T.g T.zero m).g) ≫
        (openSubspaceTensorExteriorPieceIso U AF₁ AG₃ BF₁ BG₃ k ((m + 1 : ℕ) : ℤ)).hom =
      (openSubspaceTensorExteriorPieceIso U AF₁ A₂ BF₁ B₂ k ((m + 1 : ℕ) : ℤ)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf).obj
            (BF₁.exteriorPower k)).map
          (relComplex B₂ BG₃ (T.map (openSubspaceRestriction U)).f
            (T.map (openSubspaceRestriction U)).g
            (T.map (openSubspaceRestriction U)).zero m).g :=
  map_tensorLeftFunctor_map_pieceMap_comp_openSubspaceTensorExteriorPieceIso_hom U
    AF₁ A₂ AG₃ BF₁ B₂ BG₃ T.g k ((m + 1 : ℕ) : ℤ)

/-! ### The crossing of the splitting-free comparison at the quotient level -/

/-- **The presentation of [Stacks, Tag 01CJ] restricted to an open subspace**: the short complex
`T.X₁|_U ⟶ T.X₂|_U ⟶ T.X₃|_U` of the restrictions of `T.f` and `T.g`.

It is `CategoryTheory.ShortComplex.map` of `T` along `SheafOfModules.openSubspaceRestriction`, and
equal to it by `rfl` — the `zero` field is literally that complex's. What the re-typing buys is
the *spelling* of the ambient category: here it is `CategoryTheory.Sheaf.toRingCat` of the open
subspace's sheaf of rings, which is the one `SheafOfModules.exteriorGradedQuotientHom` is stated
over and the one the bundles of algebras chosen on `U` are stated over, whereas the target
category of `SheafOfModules.openSubspaceRestriction` is spelled with
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf`. -/
def openSubspaceShortComplex : ShortComplex (SheafOfModules.{u} (Sheaf.toRingCat
    (Opens.grothendieckTopology ↥(restrictToOpen X U).carrier) (restrictToOpen X U).sheaf)) :=
  ShortComplex.mk ((openSubspaceRestriction U).map T.f)
    ((openSubspaceRestriction U).map T.g) (T.map (openSubspaceRestriction U)).zero

/-- **The splitting-free comparison of [Stacks, Section 0FMK], read at the quotient level,
restricted to an open subspace is the one of the bundles of algebras chosen there**: read through
`SheafOfModules.openSubspaceTensorExteriorPieceIso` at the source and through
`SheafOfModules.exteriorGradedCokernelOpenSubspaceIso` at the target, the restriction of
`SheafOfModules.exteriorGradedQuotientHom` is `SheafOfModules.exteriorGradedQuotientHom` of `BF₁`,
`BG₃`, `B₂` and the restricted presentation. Nothing of either side then lives on `X`.

The comparison is not built from morphisms that cross one at a time — it is a descent along the
presentation of [Stacks, Tag 01CJ] — so what crosses is its defining equation
`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom`, at each of the two
sites, cancelled against the epimorphism
`SheafOfModules.epi_openSubspaceRestriction_map_tensorLeftFunctor_map_relComplex_g`. That is five
commuting squares in the shape of `SheafOfModules.eq_of_epi_two_ladders`: the two defining
equations, the crossing of the surjection of the section above
(`…_map_relComplex_g_comp_openSubspaceTensorExteriorPieceIso_hom`), the crossing of the ambient
morphism onto the quotient
(`SheafOfModules.openSubspaceRestriction_map_exteriorGradedHom_comp_cokernelIso`) and the crossing
of the transport between the degrees `m + 1` and `1 + m`
(`SheafOfModules.map_tensorLeftFunctor_map_eqToHom_comp_openSubspaceTensorExteriorPieceIso_hom`).

The restricted presentation is passed as `(T := SheafOfModules.openSubspaceShortComplex U)` rather
than left to the unifier, which would have to solve a projection of a metavariable against the
restriction functor's own spelling of the sheaf of rings. -/
theorem openSubspaceRestriction_map_exteriorGradedQuotientHom_comp_cokernelIso (hS : T.Exact)
    (hepi : Epi T.g) (hS' : (openSubspaceShortComplex U (T := T)).Exact)
    (hepi' : Epi (openSubspaceShortComplex U (T := T)).g) (k m : ℕ) :
    (openSubspaceRestriction U).map (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m) ≫
        (exteriorGradedCokernelOpenSubspaceIso U AF₁ A₂ BF₁ B₂ T.f (k + 1) m).hom =
      (openSubspaceTensorExteriorPieceIso U AF₁ AG₃ BF₁ BG₃ k ((m + 1 : ℕ) : ℤ)).hom ≫
        exteriorGradedQuotientHom (T := openSubspaceShortComplex U (T := T)) BF₁ BG₃ B₂ hS' hepi'
          k m :=
  eq_of_epi_two_ladders
    (epi_openSubspaceRestriction_map_tensorLeftFunctor_map_relComplex_g U AF₁ AG₃ A₂ hS hepi k m)
    _ _ _ _ _ _ _ _ _ _ _
    (mapCompEqMapComp (openSubspaceRestriction U) _ _ _ _
      (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m))
    (openSubspaceRestriction_map_exteriorGradedHom_comp_cokernelIso U AF₁ A₂ BF₁ B₂ T.f k m)
    (map_tensorLeftFunctor_map_relComplex_g_comp_openSubspaceTensorExteriorPieceIso_hom U
      AF₁ AG₃ A₂ BF₁ BG₃ B₂ k m)
    (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom
      (T := openSubspaceShortComplex U (T := T)) BF₁ BG₃ B₂ hS' hepi' k m)
    (map_tensorLeftFunctor_map_eqToHom_comp_openSubspaceTensorExteriorPieceIso_hom U
      AF₁ A₂ BF₁ B₂ k (congrArg (fun j : ℕ => (j : ℤ)) (Nat.add_comm m 1)))

/-- **The restricted quotient-level comparison of [Stacks, Section 0FMK] is a monomorphism over
an open on which the presentation of [Stacks, Tag 01CJ] splits.** This is the local input the
globalization of the section asks for, and it is where the splitting is spent.

Two steps, and nothing else. The crossing
`SheafOfModules.openSubspaceRestriction_map_exteriorGradedQuotientHom_comp_cokernelIso` reads the
restricted morphism as the one of bundles of algebras chosen on `U` conjugated by the source
identification and the cokernel identification, both isomorphisms, so
`SheafOfModules.mono_of_comp_iso_eq_iso_comp` reduces monomorphy to monomorphy of the `U`-side
morphism; and that is `SheafOfModules.mono_exteriorGradedQuotientHom_of_splitting` at the
splitting.

The bundles on `U` are not hypotheses: the statement does not mention them, and
`SheafOfModules.ringedSpaceAlgebras` of the open subspace is a canonical choice, so asking a
consumer for them would be asking for data it can always build. The short exactness and
surjectivity the `U`-side morphism needs are read off the splitting
(`CategoryTheory.ShortComplex.Splitting.exact` and `…epi_g`) rather than taken as hypotheses, for
the same reason. -/
theorem mono_openSubspaceRestriction_map_exteriorGradedQuotientHom_of_splitting (hS : T.Exact)
    (hepi : Epi T.g) (sp : (openSubspaceShortComplex U (T := T)).Splitting) (k m : ℕ) :
    Mono ((openSubspaceRestriction U).map (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m)) :=
  mono_of_comp_iso_eq_iso_comp _ _
    (openSubspaceRestriction_map_exteriorGradedQuotientHom_comp_cokernelIso U AF₁ AG₃ A₂
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₁))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₃))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₂))
      hS hepi sp.exact sp.epi_g k m)
    (mono_exteriorGradedQuotientHom_of_splitting (T := openSubspaceShortComplex U (T := T))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₁))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₃))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₂))
      sp.exact sp.epi_g sp k m)

end RelComplex

/-! ### Invertibility of the splitting-free comparison is local -/

section Locality

variable {X : Scheme.{u}}
  {T : ShortComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
  (AF₁ : TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.toRingedSpace.carrier) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.toRingedSpace.carrier) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.toRingedSpace.carrier) T.X₂)

/-- **The splitting-free comparison of [Stacks, Section 0FMK] is an isomorphism as soon as its
quotient-level form is a monomorphism over the members of an open covering.**

This is the globalization step of Section 0FMK, with the local input reduced as far as it goes.
Three reductions are at work, and each of them removes something from what has to be carried
across restriction to an open:

* **Invertibility is replaced by monomorphy.** The comparison is an epimorphism with no hypothesis
  at all (`SheafOfModules.epi_exteriorGradedQuotientComparison`), and sheaves of modules are
  balanced (`Stacks.SheafOfModules.TopWedge.balanced_sheafOfModules`), so only the injectivity
  half is local.
* **The graded piece is replaced by the ambient quotient.** Monomorphy of the comparison follows
  from monomorphy of `SheafOfModules.exteriorGradedQuotientHom`
  (`SheafOfModules.mono_exteriorGradedQuotientComparison_of_mono_quotientHom`), whose target is
  `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` and carries no `CategoryTheory.Limits.imageSubobject`. One functor fewer
  has to be crossed, which is what the implementation notes of
  `StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece` say that morphism is for.
* **Monomorphy is local for the composite spelling of restriction.** It is local for Mathlib's
  restriction along the open immersion
  (`Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover`) and transports from the
  composite spelling to that one
  (`SheafOfModules.mono_restrictFunctor_map_of_mono_openSubspaceRestriction_map`), and the
  composite spelling is where the exterior algebra crosses restriction.

The covering is given pointwise, as an open neighbourhood of each point of `X`; that is the form
in which [Stacks, Section 0FMK] produces one, the transitivity sequence of a smooth morphism
splitting over a neighbourhood of every point. -/
theorem isIso_exteriorGradedQuotientComparison_of_mono_restrict (hS : T.Exact) (hepi : Epi T.g)
    (k m : ℕ)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((openSubspaceRestriction (X := X.toRingedSpace) U).map
        (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m))) :
    IsIso (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  have := Stacks.SheafOfModules.TopWedge.balanced_sheafOfModules
    (X := X.toRingedSpace.carrier) (Osharp := ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)
  have := epi_exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m
  have : Mono (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
    mono_exteriorGradedQuotientComparison_of_mono_quotientHom AF₁ AG₃ A₂ hS hepi k m
      (Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover
        (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m)
        (fun x : X => (H x).choose.ι)
        (fun x => ⟨x, ⟨x, (H x).choose_spec.1⟩, rfl⟩)
        (fun x => mono_restrictFunctor_map_of_mono_openSubspaceRestriction_map X (H x).choose
          (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m) (H x).choose_spec.2))
  isIso_of_mono_of_epi _

/-- **The splitting-free comparison of [Stacks, Section 0FMK] is an isomorphism as soon as the
presentation of [Stacks, Tag 01CJ] splits over the members of an open covering**:

`⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ≅ gr^k⋀ⁿT.X₂`,  `n = k + 1 + m`,

for a short exact `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` of `𝒪_X`-modules on a scheme which splits over
an open neighbourhood of every point. No splitting of the sequence itself is assumed, and no
compatibility of the comparison with restriction is left to the consumer: this is the
globalization of the section, carried out.

It is `SheafOfModules.isIso_exteriorGradedQuotientComparison_of_mono_restrict` — invertibility
follows from monomorphy of the quotient-level form over a covering — fed with
`SheafOfModules.mono_openSubspaceRestriction_map_exteriorGradedQuotientHom_of_splitting` at each
member of the covering.

The covering is given pointwise, and its splittings are of
`SheafOfModules.openSubspaceShortComplex`, the presentation restricted to the open and re-typed at
the open subspace's own spelling of its sheaf of rings. That is deliberate and not an artefact:
`CategoryTheory.ShortComplex.map` of `SheafOfModules.openSubspaceRestriction` cannot be written
in the same statement as `CategoryTheory.ShortComplex.map` of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, each functor's `PreservesZeroMorphisms` being
findable only at its own spelling of the category of modules on `X`. A consumer holding a
splitting of the latter converts it with
`SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor`. -/
theorem isIso_exteriorGradedQuotientComparison_of_locally_split (hS : T.Exact) (hepi : Epi T.g)
    (k m : ℕ)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (openSubspaceShortComplex (X := X.toRingedSpace) U (T := T)).Splitting) :
    IsIso (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  isIso_exteriorGradedQuotientComparison_of_mono_restrict AF₁ AG₃ A₂ hS hepi k m
    (fun x => ⟨(H x).choose, (H x).choose_spec.1,
      mono_openSubspaceRestriction_map_exteriorGradedQuotientHom_of_splitting (H x).choose
        AF₁ AG₃ A₂ hS hepi (H x).choose_spec.2.some k m⟩)

end Locality

end SheafOfModules

end
