module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import StacksFrontier.Algebra.Homology.Resolution.Existence
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopyLift
public import StacksFrontier.AlgebraicTopology.SimplicialObject.HomotopyEquivalenceProjectivity
import all StacksFrontier.Homology.KFlat.FreeResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived functors of the exterior square

Let `A` be a commutative ring. The exterior square `Λ² : M ↦ ⋀²_A M` is not an additive functor,
so its derived functors are not computed by applying it to a projective resolution as a chain
complex. Following Dold and Puppe they are computed simplicially: a *simplicial projective
resolution* of `M` is a simplicial module `P` with projective terms whose Moore complex `s(P)` is
quasi-isomorphic to `M` placed in degree `0`, and

  `LΛ²(P) = s(Λ²(P))`, `LᵢΛ²_A(M) = Hᵢ(s(Λ²(P)))`,

where `Λ²(P)` is the simplicial module obtained by applying `Λ²` termwise.

Nothing in the construction uses that the functor is `Λ²`, nor that the category is one of
modules, so it is carried out for an arbitrary functor `F : C ⥤ D` out of an abelian category
`C`, with `D` preadditive with homology. The key facts are the following.

* Every morphism `g : X ⟶ Y` lifts to a morphism `f : P ⟶ Q` of simplicial objects between
  simplicial projective resolutions of `X` and `Y`, and any two lifts are simplicially homotopic.
  Under the Dold–Kan correspondence the normalized Moore complex `N(P)` is a projective
  resolution of `X`; lifts of `g` to `N(P) ⟶ N(Q)` exist and are unique up to chain homotopy, the
  normalized Moore complex functor is an equivalence, and chain homotopies between maps of
  normalized Moore complexes come from simplicial homotopies.
* Any functor `F` preserves simplicial homotopies, and simplicially homotopic maps induce chain
  homotopic maps of Moore complexes. Hence `Hᵢ(s(F(P)))` does not depend on `P` up to canonical
  isomorphism, and it is functorial in `X`: this is the simplicial left derived functor `LᵢF`.
* Every object of an abelian category with enough projectives has a simplicial projective
  resolution, namely `Γ(K)` for a projective resolution `K`, with `Γ` the Dold–Kan functor; a
  module has one with free terms.
* An isomorphism `F ⋙ H ≅ G ⋙ F'`, for functors `F : C ⥤ D`, `F' : C' ⥤ D'`, `G : C ⥤ C'`
  and `H : D ⥤ D'` with `H` additive and preserving homology, induces
  `H(LᵢF(X)) ≅ LᵢF'(G(X))` whenever `G` carries a simplicial projective resolution of `X` to one
  of `G(X)`, as it does when `G` is additive and preserves homology and projective objects. The
  comparison is natural in `X`, transitive for pasted squares, natural in the pair `(G, H)`, and
  trivial for the identity square.
* `P₁ ⇉ P₀ → X` is a reflexive coequalizer. If `F` carries it to a coequalizer then
  `L₀F(X) ≅ F(X)`. The exterior powers of modules preserve reflexive coequalizers, so
  `L₀Λ²(M) ≅ ⋀² M`.

## Main definitions

* `Stacks.SimplicialProjectiveResolution X`: a simplicial projective resolution of `X`.
* `Stacks.SimplicialProjectiveResolution.IsLift`: a morphism of simplicial objects lying over a
  morphism of the resolved objects.
* `Stacks.SimplicialProjectiveResolution.derivedComplex F P`: the complex `s(F(P))`, and
  `Stacks.SimplicialProjectiveResolution.derivedHomology F P i` its homology `Hᵢ(s(F(P)))`.
* `Stacks.SimplicialProjectiveResolution.derivedMap F g P Q i`: the map `Hᵢ(s(F(P))) ⟶ Hᵢ(s(F(Q)))`
  induced by `g`, and `Stacks.SimplicialProjectiveResolution.derivedIso F P Q i` the comparison
  isomorphism between two resolutions of the same object.
* `Stacks.simplicialLeftDerived F i`: the simplicial left derived functor `LᵢF : C ⥤ D`.
* `Stacks.SimplicialProjectiveResolution.mapOfQuasiIso` and
  `Stacks.SimplicialProjectiveResolution.map`: the image of a simplicial projective resolution
  under a functor.
* `Stacks.derivedHomologyMapIso` and `Stacks.SimplicialProjectiveResolution.mapDerivedHomologyIso`:
  the comparison `H(LᵢF(X)) ≅ LᵢF'(G(X))`, and `Stacks.pasteIso` the pasting of two squares of
  functors.
* `HomologicalComplex.mapHomologyIso`: the homology of the image of a complex under a functor
  preserving homology, and `AlgebraicTopology.alternatingFaceMapComplexCompIso`: the Moore
  complex of the image of a simplicial object under an additive functor.
* `Stacks.DerivedSquare.complex P` and `Stacks.DerivedSquare.homology P i`: the complex `LΛ²(P)`
  and the derived exterior square `LᵢΛ²(M)` computed from a resolution `P` of `M`, and
  `Stacks.DerivedSquare.functor R i`: the functor `LᵢΛ²` on `R`-modules.

## Main results

* `Stacks.SimplicialProjectiveResolution.exists_isLift` and
  `Stacks.SimplicialProjectiveResolution.IsLift.nonempty_homotopy`: lifts exist and are unique up
  to simplicial homotopy.
* `Stacks.SimplicialProjectiveResolution.IsLift.homotopyEquivalences`: two simplicial projective
  resolutions of the same object are homotopy equivalent compatibly with the augmentations, and
  `Stacks.SimplicialProjectiveResolution.IsLift.homotopyEquivalences_derivedComplexMap`: so are the
  complexes `s(F(P))` and `s(F(Q))`.
* `Stacks.SimplicialProjectiveResolution.derivedMap_id`,
  `Stacks.SimplicialProjectiveResolution.derivedMap_comp` and
  `Stacks.SimplicialProjectiveResolution.derivedIso_trans`: functoriality and compatibility of the
  comparison isomorphisms with composition.
* `Stacks.SimplicialProjectiveResolution.ofProjectiveResolution` and
  `Stacks.SimplicialProjectiveResolution.exists_free`: existence of simplicial projective
  resolutions, with free terms for modules.
* `exteriorPower.range_map_sub_map_eq_ker_map`: `⋀ⁿ` preserves reflexive coequalizers of modules.
* `Stacks.SimplicialProjectiveResolution.derivedHomologyZeroIso`: `L₀F(X) ≅ F(X)` when `F` is
  right exact on the resolution, and `Stacks.DerivedSquare.homologyZeroIso`,
  `Stacks.DerivedSquare.functorZeroIso`: `L₀Λ² ≅ Λ²`, naturally.
* `Stacks.SimplicialProjectiveResolution.map_derivedMap_comp_mapDerivedHomologyIso_hom`,
  `Stacks.SimplicialProjectiveResolution.app_comp_mapDerivedHomologyIso_hom`,
  `Stacks.SimplicialProjectiveResolution.mapDerivedHomologyIso_pasteIso_hom` and
  `Stacks.SimplicialProjectiveResolution.mapDerivedHomologyIso_refl_hom`: naturality,
  transitivity and triviality of the comparison along a change of categories.
* `CategoryTheory.ShortComplex.ShortExact.map_alternatingFaceMapComplex_of_app`: a degreewise
  short exact sequence of simplicial objects gives a short exact sequence of Moore complexes.

## Implementation notes

The resolutions are required to have projective rather than free terms: this is the hypothesis
the comparison argument uses, it is stable under base change and under reduction modulo an
element, and a resolution with free terms is in particular one with projective terms. The
augmentation is recorded as a quasi-isomorphism from the Moore complex `s(P)` to `X` in degree
`0`, rather than as a morphism to the constant simplicial object. The derived objects are
defined for an arbitrary resolution together with comparison isomorphisms, rather than for a
single chosen one, so that a resolution adapted to a given situation may be used.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe v u v' u' v'' u''

/-! ### Moore complexes in low degree -/

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C]

/-- The first differential of the alternating face map complex is `d₀ - d₁`. -/
@[sga "4 V 1.10" "1.10.5 in degree 1 → 0"]
lemma alternatingFaceMapComplex_obj_d_one_zero [Preadditive C] (P : SimplicialObject C) :
    ((alternatingFaceMapComplex C).obj P).d 1 0 = P.δ 0 - P.δ 1 := by
  simp [Fin.sum_univ_two, sub_eq_add_neg]

variable [Abelian C]

/-- The inclusion of the normalized Moore complex into the alternating face map complex is a
quasi-isomorphism. -/
instance quasiIso_inclusionOfMooreComplexMap (P : SimplicialObject C) :
    QuasiIso (inclusionOfMooreComplexMap P) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.quasiIso_hom

/-- The projection of the alternating face map complex onto the normalized Moore complex is a
quasi-isomorphism. -/
instance quasiIso_PInftyToNormalizedMooreComplex (P : SimplicialObject C) :
    QuasiIso (DoldKan.PInftyToNormalizedMooreComplex P) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.quasiIso_inv

/-- In degree `0` the inclusion of the normalized Moore complex is a split epimorphism. -/
instance epi_inclusionOfMooreComplexMap_f_zero (P : SimplicialObject C) :
    Epi ((inclusionOfMooreComplexMap P).f 0) := by
  refine @IsSplitEpi.epi _ _ _ _ _
    (IsSplitEpi.mk' ⟨(DoldKan.PInftyToNormalizedMooreComplex P).f 0, ?_⟩)
  exact (HomologicalComplex.congr_hom
    (DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap P) 0).trans
      DoldKan.PInfty_f_0

end AlgebraicTopology

/-! ### Short exact sequences of simplicial objects -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short complex of simplicial objects which is short exact in each degree gives a short exact
sequence of alternating face map complexes. -/
theorem map_alternatingFaceMapComplex_of_app {T : ShortComplex (SimplicialObject C)}
    (hT : ∀ n : ℕ, (T.map ((evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋n⦌))).ShortExact) :
    (T.map (alternatingFaceMapComplex C)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ hT

/-- A short exact sequence of simplicial objects gives a short exact sequence of alternating
face map complexes. -/
theorem map_alternatingFaceMapComplex {T : ShortComplex (SimplicialObject C)}
    (hT : T.ShortExact) : (T.map (alternatingFaceMapComplex C)).ShortExact :=
  map_alternatingFaceMapComplex_of_app fun n =>
    hT.map_of_exact ((evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋n⦌))

end CategoryTheory.ShortComplex.ShortExact

/-! ### Functors preserving homology -/

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/-- A functor preserving homology carries the inclusion of the cycles to a monomorphism. -/
instance mono_map_iCycles (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [F.PreservesHomology] :
    Mono (F.map S.iCycles) := by
  have h := S.mapCyclesIso_hom_iCycles F
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  infer_instance

-- A composite of functors preserving homology preserves homology
-- (`CategoryTheory.Functor.preservesHomology_comp`, StacksFrontier/Algebra/Homology/ShortComplex/MapHomologyComp.lean), as an instance here.
attribute [instance] CategoryTheory.Functor.preservesHomology_comp

/-- The identification of cycles for a composite of functors preserving homology is the
composite of the identifications. -/
lemma mapCyclesIso_comp (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesHomology] [G.PreservesHomology] :
    (S.mapCyclesIso (F ⋙ G)).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom := by
  rw [← cancel_mono ((F ⋙ G).map S.iCycles), mapCyclesIso_hom_iCycles, Category.assoc]
  show _ = _ ≫ G.map _ ≫ G.map (F.map S.iCycles)
  rw [← G.map_comp, mapCyclesIso_hom_iCycles, mapCyclesIso_hom_iCycles]
  rfl

/-- The identifications of cycles are natural in the functor. -/
@[reassoc]
lemma cyclesMap_mapNatTrans_comp_mapCyclesIso_hom (S : ShortComplex C) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) :
    cyclesMap (S.mapNatTrans τ) ≫ (S.mapCyclesIso G).hom =
      (S.mapCyclesIso F).hom ≫ τ.app S.cycles := by
  rw [← cancel_mono (G.map S.iCycles), Category.assoc, mapCyclesIso_hom_iCycles, cyclesMap_i,
    Category.assoc, ← τ.naturality, mapCyclesIso_hom_iCycles_assoc]
  rfl

/-- The identifications of homology are natural in the functor. -/
@[reassoc]
lemma homologyMap_mapNatTrans_comp_mapHomologyIso_hom (S : ShortComplex C) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) :
    homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology := by
  rw [← cancel_epi ((S.map F).homologyπ), homologyπ_naturality_assoc,
    homologyπ_comp_mapHomologyIso_hom, cyclesMap_mapNatTrans_comp_mapCyclesIso_hom_assoc,
    homologyπ_comp_mapHomologyIso_hom_assoc, τ.naturality]

/-- The identification of cycles for the identity functor is the identity. -/
@[simp]
lemma mapCyclesIso_id (S : ShortComplex C) : (S.mapCyclesIso (𝟭 C)).hom = 𝟙 _ := by
  rw [← cancel_mono ((𝟭 C).map S.iCycles), mapCyclesIso_hom_iCycles, Category.id_comp]
  rfl

/-- The identification of homology for the identity functor is the identity. -/
@[simp]
lemma mapHomologyIso_id (S : ShortComplex C) : (S.mapHomologyIso (𝟭 C)).hom = 𝟙 _ := by
  rw [← cancel_epi ((S.map (𝟭 C)).homologyπ), homologyπ_comp_mapHomologyIso_hom, mapCyclesIso_id,
    Category.id_comp, Category.comp_id]
  rfl

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E] {ι : Type*} {c : ComplexShape ι}

/-- For a functor `F` preserving homology, the homology of the complex `F(K)` is `F` applied to
the homology of `K`. -/
def mapHomologyIso (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (i : ι) : ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  (K.sc i).mapHomologyIso F

/-- The identification `mapHomologyIso` is natural in the complex. -/
@[reassoc]
lemma homologyMap_map_comp_mapHomologyIso_hom {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (i : ι) :
    homologyMap ((F.mapHomologicalComplex c).map φ) i ≫ (L.mapHomologyIso F i).hom =
      (K.mapHomologyIso F i).hom ≫ F.map (homologyMap φ i) :=
  ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor C c i).map φ) F

/-- The identification `mapHomologyIso` is natural in the complex. -/
@[reassoc]
lemma map_homologyMap_comp_mapHomologyIso_inv {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (i : ι) :
    F.map (homologyMap φ i) ≫ (L.mapHomologyIso F i).inv =
      (K.mapHomologyIso F i).inv ≫ homologyMap ((F.mapHomologicalComplex c).map φ) i := by
  rw [Iso.comp_inv_eq, Category.assoc, homologyMap_map_comp_mapHomologyIso_hom,
    Iso.inv_hom_id_assoc]

/-- The identification `mapHomologyIso` for a composite of functors is the composite of the
identifications. -/
lemma mapHomologyIso_comp (K : HomologicalComplex C c) (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (i : ι) :
    (K.mapHomologyIso (F ⋙ G) i).hom =
      (((F.mapHomologicalComplex c).obj K).mapHomologyIso G i).hom ≫
        G.map (K.mapHomologyIso F i).hom :=
  (K.sc i).mapHomologyIso_comp_hom F G

/-- The inverse of `mapHomologyIso` for a composite of functors. -/
lemma mapHomologyIso_comp_inv (K : HomologicalComplex C c) (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (i : ι) :
    (K.mapHomologyIso (F ⋙ G) i).inv =
      G.map (K.mapHomologyIso F i).inv ≫
        (((F.mapHomologicalComplex c).obj K).mapHomologyIso G i).inv := by
  rw [← cancel_epi (K.mapHomologyIso (F ⋙ G) i).hom, Iso.hom_inv_id, mapHomologyIso_comp,
    Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp,
    Iso.hom_inv_id]

/-- The identification `mapHomologyIso` is natural in the functor. -/
@[reassoc]
lemma homologyMap_app_comp_mapHomologyIso_hom (K : HomologicalComplex C c) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) (i : ι) :
    homologyMap ((NatTrans.mapHomologicalComplex τ c).app K) i ≫ (K.mapHomologyIso G i).hom =
      (K.mapHomologyIso F i).hom ≫ τ.app (K.homology i) :=
  (K.sc i).homologyMap_mapNatTrans_comp_mapHomologyIso_hom τ

/-- The identification `mapHomologyIso` is natural in the functor. -/
@[reassoc]
lemma app_comp_mapHomologyIso_inv (K : HomologicalComplex C c) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) (i : ι) :
    τ.app (K.homology i) ≫ (K.mapHomologyIso G i).inv =
      (K.mapHomologyIso F i).inv ≫ homologyMap ((NatTrans.mapHomologicalComplex τ c).app K) i := by
  rw [Iso.comp_inv_eq, Category.assoc, homologyMap_app_comp_mapHomologyIso_hom,
    Iso.inv_hom_id_assoc]

/-- The identification `mapHomologyIso` for the identity functor is the identity. -/
@[simp]
lemma mapHomologyIso_id (K : HomologicalComplex C c) (i : ι) :
    (K.mapHomologyIso (𝟭 C) i).hom = 𝟙 _ :=
  (K.sc i).mapHomologyIso_id

/-- The identification `mapHomologyIso` for the identity functor is the identity. -/
@[simp]
lemma mapHomologyIso_id_inv (K : HomologicalComplex C c) (i : ι) :
    (K.mapHomologyIso (𝟭 C) i).inv = 𝟙 _ := by
  rw [← cancel_epi (K.mapHomologyIso (𝟭 C) i).hom, Iso.hom_inv_id, mapHomologyIso_id,
    Category.comp_id]

end HomologicalComplex

/-! ### The Moore complex and functors -/

namespace AlgebraicTopology

variable {D : Type u} [Category.{v} D] [Preadditive D] {D' : Type u'} [Category.{v'} D']
  [Preadditive D']

/-- The alternating face map complex of `K ⋙ H` is the image under the additive functor `H` of
the alternating face map complex of `K`. -/
def alternatingFaceMapComplexCompIso (K : SimplicialObject D) (H : D ⥤ D') [H.Additive] :
    (alternatingFaceMapComplex D').obj (K ⋙ H) ≅
      (H.mapHomologicalComplex _).obj ((alternatingFaceMapComplex D).obj K) :=
  eqToIso (Functor.congr_obj (map_alternatingFaceMapComplex H) K).symm

/-- The components of `alternatingFaceMapComplexCompIso` are identities. -/
@[simp]
lemma alternatingFaceMapComplexCompIso_hom_f (K : SimplicialObject D) (H : D ⥤ D') [H.Additive]
    (n : ℕ) : (alternatingFaceMapComplexCompIso K H).hom.f n = 𝟙 _ := by
  simp [alternatingFaceMapComplexCompIso, HomologicalComplex.eqToHom_f]

/-- The components of the inverse of `alternatingFaceMapComplexCompIso` are identities. -/
@[simp]
lemma alternatingFaceMapComplexCompIso_inv_f (K : SimplicialObject D) (H : D ⥤ D') [H.Additive]
    (n : ℕ) : (alternatingFaceMapComplexCompIso K H).inv.f n = 𝟙 _ := by
  simp [alternatingFaceMapComplexCompIso, HomologicalComplex.eqToHom_f]

end AlgebraicTopology

/-! ### Exterior powers preserve reflexive coequalizers -/

namespace exteriorPower

variable {R : Type*} [CommRing R] {P N M : Type*} [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

/-- Let `q : N → M` be surjective. Every submodule of `⋀ⁿ N` containing the wedges `v₁ ∧ ⋯ ∧ vₙ`
with some `vᵢ ∈ ker q` contains the kernel of `⋀ⁿ q`. -/
theorem ker_map_le_of_surjective {q : N →ₗ[R] M} (hq : Function.Surjective q) {n : ℕ}
    (W : Submodule R (⋀[R]^n N))
    (hW : ∀ (v : Fin n → N) (i : Fin n), q (v i) = 0 → ιMulti R n v ∈ W) :
    LinearMap.ker (map n q) ≤ W := by
  let σ := Function.surjInv hq
  have hσ : ∀ m, q (σ m) = m := Function.surjInv_eq hq
  have key : ∀ [DecidableEq (Fin n)] (w : Fin n → N) (i : Fin n) (x x' : N), q x = q x' →
      ιMulti R n (Function.update w i x) - ιMulti R n (Function.update w i x') ∈ W := by
    intro _ w i x x' h
    rw [← AlternatingMap.map_update_sub]
    exact hW _ i (by simp [h])
  let φ : M [⋀^Fin n]→ₗ[R] (⋀[R]^n N ⧸ W) :=
    { toFun := fun v => W.mkQ (ιMulti R n (σ ∘ v))
      map_update_add' := fun v i x y => by
        simp only [Function.comp_update]
        rw [← map_add, ← AlternatingMap.map_update_add]
        exact (Submodule.Quotient.eq W).2 (key _ i _ _ (by simp [hσ]))
      map_update_smul' := fun v i c x => by
        simp only [Function.comp_update]
        rw [← map_smul, ← AlternatingMap.map_update_smul]
        exact (Submodule.Quotient.eq W).2 (key _ i _ _ (by simp [hσ]))
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [(ιMulti R n).map_eq_zero_of_eq (σ ∘ v) (i := i) (j := j) (by simp [h]) hij] }
  have hφ : alternatingMapLinearEquiv φ ∘ₗ map n q = W.mkQ := by
    refine linearMap_ext (AlternatingMap.ext fun w => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, map_apply_ιMulti,
      alternatingMapLinearEquiv_apply_ιMulti]
    refine (Submodule.Quotient.eq W).2 ?_
    have := (ιMulti R n).toMultilinearMap.map_piecewise_sub_map_piecewise (σ ∘ q ∘ w) w w
      Finset.univ
    simp only [Finset.piecewise_univ, AlternatingMap.coe_multilinearMap] at this
    rw [this]
    exact Submodule.sum_mem _ fun i _ => hW _ i (by simp [hσ])
  intro x hx
  have h := LinearMap.congr_fun hφ x
  rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hx, map_zero] at h
  exact (Submodule.Quotient.mk_eq_zero W).1 h.symm

/-- **Exterior powers preserve reflexive coequalizers.** Let `a, b : P → N` be linear maps with
a common set-theoretic section (every `y : N` is `a z = b z` for some `z`), and let `q : N → M`
be a surjection with kernel the image of `a - b`, so that `M` is the coequalizer of `a` and `b`.
Then `⋀ⁿ q` is surjective with kernel the image of `⋀ⁿ a - ⋀ⁿ b`: `⋀ⁿ M` is the coequalizer of
`⋀ⁿ a` and `⋀ⁿ b`. -/
theorem range_map_sub_map_eq_ker_map {a b : P →ₗ[R] N} {q : N →ₗ[R] M}
    (hq : Function.Surjective q) (hab : LinearMap.range (a - b) = LinearMap.ker q)
    (hs : ∀ y : N, ∃ z : P, a z = y ∧ b z = y) (n : ℕ) :
    LinearMap.range (map n a - map n b) = LinearMap.ker (map n q) := by
  have hqab : q ∘ₗ a = q ∘ₗ b := by
    ext z
    have : (a - b) z ∈ LinearMap.ker q := hab ▸ LinearMap.mem_range_self _ z
    simpa [sub_eq_zero] using this
  refine le_antisymm ?_ (ker_map_le_of_surjective hq _ fun v i hv => ?_)
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← map_comp, ← map_comp, hqab, sub_self]
  · obtain ⟨z, hz⟩ : v i ∈ LinearMap.range (a - b) := hab ▸ hv
    choose s hsa hsb using hs
    let u := Function.update (s ∘ v) i z
    have hu : ∀ c : P →ₗ[R] N, (∀ j, c (s (v j)) = v j) →
        c ∘ u = Function.update v i (c z) := fun c hc => by
      ext j
      rcases eq_or_ne j i with rfl | hj
      · simp [u]
      · simp [u, hj, hc]
    refine ⟨ιMulti R n u, ?_⟩
    rw [LinearMap.sub_apply, map_apply_ιMulti, map_apply_ιMulti, hu a (fun j => hsa _),
      hu b (fun j => hsb _), ← AlternatingMap.map_update_sub, ← LinearMap.sub_apply, hz,
      Function.update_eq_self]

end exteriorPower

namespace Stacks

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A *simplicial projective resolution* of an object `X` of an abelian category `C`: a
simplicial object `P` of `C` whose terms `Pₙ` are projective, together with a
quasi-isomorphism `π` from its alternating face map (Moore) complex to `X` placed in
degree `0`. -/
structure SimplicialProjectiveResolution (X : C) where
  /-- The simplicial object of the resolution. -/
  obj : SimplicialObject C
  /-- Every term of the resolution is projective. -/
  projective (n : ℕ) : Projective (obj _⦋n⦌) := by infer_instance
  /-- The augmentation, as a morphism from the Moore complex to `X` in degree `0`. -/
  π : (alternatingFaceMapComplex C).obj obj ⟶ (ChainComplex.single₀ C).obj X
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso π := by infer_instance

attribute [instance] SimplicialProjectiveResolution.projective
  SimplicialProjectiveResolution.quasiIso

namespace SimplicialProjectiveResolution

variable {X Y Z : C}

/-- The terms of the normalized Moore complex of a simplicial projective resolution are
projective: they are retracts of the terms of the resolution. -/
instance projective_normalizedMooreComplex_X (P : SimplicialProjectiveResolution X) (n : ℕ) :
    Projective (((normalizedMooreComplex C).obj P.obj).X n) :=
  @Retract.projective _ _ _ (P.obj _⦋n⦌)
    { i := (inclusionOfMooreComplexMap P.obj).f n
      r := (DoldKan.PInftyToNormalizedMooreComplex P.obj).f n
      retract := HomologicalComplex.congr_hom
        (DoldKan.splitMonoInclusionOfMooreComplexMap P.obj).id n } (P.projective n)

/-- The projective resolution of `X` given by the normalized Moore complex of a simplicial
projective resolution. -/
abbrev normalized (P : SimplicialProjectiveResolution X) : ProjectiveResolution X where
  complex := (normalizedMooreComplex C).obj P.obj
  π := inclusionOfMooreComplexMap P.obj ≫ P.π
  quasiIso := quasiIso_comp _ _

/-- The augmentation `P₀ ⟶ X` of a simplicial projective resolution, the degree `0` component
of `P.π`. -/
def ε (P : SimplicialProjectiveResolution X) : P.obj _⦋0⦌ ⟶ X := P.π.f 0

/-- A morphism `f : P ⟶ Q` of simplicial objects *lies over* `g : X ⟶ Y` if it is compatible
with the augmentations. -/
def IsLift (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (g : X ⟶ Y) (f : P.obj ⟶ Q.obj) : Prop :=
  (alternatingFaceMapComplex C).map f ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map g

variable {P : SimplicialProjectiveResolution X} {Q : SimplicialProjectiveResolution Y}
  {S : SimplicialProjectiveResolution Z}

/-- A morphism lies over `g` exactly when it is compatible with the augmentations in degree
`0`. -/
lemma isLift_iff (g : X ⟶ Y) (f : P.obj ⟶ Q.obj) :
    IsLift P Q g f ↔ f.app (op ⦋0⦌) ≫ Q.ε = P.ε ≫ g := by
  refine ⟨fun h => ?_, fun h => HomologicalComplex.to_single_hom_ext ?_⟩
  · simpa [ε] using HomologicalComplex.congr_hom h 0
  · simpa [ε] using h

/-- The identity lies over the identity. -/
lemma isLift_id (P : SimplicialProjectiveResolution X) : IsLift P P (𝟙 X) (𝟙 P.obj) := by
  simp [IsLift]

/-- Composites of lifts are lifts of the composite. -/
lemma IsLift.comp {g : X ⟶ Y} {g' : Y ⟶ Z} {f : P.obj ⟶ Q.obj} {f' : Q.obj ⟶ S.obj}
    (hf : IsLift P Q g f) (hf' : IsLift Q S g' f') : IsLift P S (g ≫ g') (f ≫ f') := by
  unfold IsLift at *
  rw [Functor.map_comp, Category.assoc, hf', reassoc_of% hf, Functor.map_comp]

/-- In degree `0` the augmentation of the normalized resolution is the restriction of `ε`. -/
lemma normalized_π_f_zero (P : SimplicialProjectiveResolution X) :
    P.normalized.π.f 0 = (inclusionOfMooreComplexMap P.obj).f 0 ≫ P.ε := rfl

/-- A morphism lies over `g` exactly when the induced map of normalized Moore complexes lies over
`g` as a map of projective resolutions. -/
lemma isLift_iff_normalized (g : X ⟶ Y) (f : P.obj ⟶ Q.obj) :
    IsLift P Q g f ↔ (normalizedMooreComplex C).map f ≫ Q.normalized.π =
      P.normalized.π ≫ (ChainComplex.single₀ C).map g := by
  have hnat : (normalizedMooreComplex C).map f ≫ inclusionOfMooreComplexMap Q.obj =
      inclusionOfMooreComplexMap P.obj ≫ (alternatingFaceMapComplex C).map f :=
    (inclusionOfMooreComplex C).naturality f
  simp only [normalized, reassoc_of% hnat, Category.assoc]
  refine ⟨fun h => by rw [h], fun h => HomologicalComplex.to_single_hom_ext ?_⟩
  have h0 := HomologicalComplex.congr_hom h 0
  simp only [HomologicalComplex.comp_f] at h0
  exact (cancel_epi _).1 h0

/-- **Existence of lifts.** Every morphism `g : X ⟶ Y` lifts to a morphism of simplicial
objects between any simplicial projective resolutions of `X` and of `Y`. -/
theorem exists_isLift (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (g : X ⟶ Y) : ∃ f : P.obj ⟶ Q.obj, IsLift P Q g f := by
  have : (normalizedMooreComplex C).IsEquivalence :=
    inferInstanceAs (CategoryTheory.Abelian.DoldKan.equivalence (A := C)).functor.IsEquivalence
  let φ : (normalizedMooreComplex C).obj P.obj ⟶ (normalizedMooreComplex C).obj Q.obj :=
    ProjectiveResolution.lift g P.normalized Q.normalized
  refine ⟨(normalizedMooreComplex C).preimage φ, ?_⟩
  rw [isLift_iff_normalized, Functor.map_preimage]
  exact ProjectiveResolution.lift_commutes g _ _

/-- **Uniqueness of lifts up to homotopy.** Two lifts of the same morphism `g : X ⟶ Y` between
simplicial projective resolutions are simplicially homotopic. -/
theorem IsLift.nonempty_homotopy {g : X ⟶ Y} {f f' : P.obj ⟶ Q.obj} (hf : IsLift P Q g f)
    (hf' : IsLift P Q g f') : Nonempty (SimplicialObject.Homotopy f f') := by
  rw [isLift_iff_normalized] at hf hf'
  obtain ⟨K, -⟩ := SimplicialObject.exists_homotopy_of_homotopy_normalizedMooreComplex_map
    (ProjectiveResolution.liftHomotopy g (P := P.normalized) (Q := Q.normalized) _ _ hf hf')
  exact ⟨K⟩

/-- **Any two simplicial projective resolutions are homotopy equivalent.** A lift
`f : P ⟶ Q` of the identity of `X` is a homotopy equivalence of simplicial objects: a lift
`f' : Q ⟶ P` of the identity is a homotopy inverse, since `f ≫ f'` and `f' ≫ f` lift the identity
as `𝟙 P` and `𝟙 Q` do. -/
theorem IsLift.homotopyEquivalences {P Q : SimplicialProjectiveResolution X}
    {f : P.obj ⟶ Q.obj} (hf : IsLift P Q (𝟙 X) f) : SimplicialObject.homotopyEquivalences C f := by
  obtain ⟨f', hf'⟩ := exists_isLift Q P (𝟙 X)
  have h₁ := hf.comp hf'
  have h₂ := hf'.comp hf
  rw [Category.comp_id] at h₁ h₂
  exact ⟨f', .rel _ _ (h₁.nonempty_homotopy (isLift_id P)),
    .rel _ _ (h₂.nonempty_homotopy (isLift_id Q))⟩

/-- The simplicial projective resolution `Γ(K)` of `X` obtained from a projective resolution
`K ⟶ X` by the Dold–Kan functor `Γ`: its normalized Moore complex is `K`, and its terms are finite
coproducts of terms of `K`. -/
def ofProjectiveResolution (K : ProjectiveResolution X) : SimplicialProjectiveResolution X where
  obj := CategoryTheory.Abelian.DoldKan.Γ.obj K.complex
  projective n := @projective_sigma _ _ _ _ _ fun _ => K.projective _
  π := DoldKan.PInftyToNormalizedMooreComplex _ ≫
    ((CategoryTheory.Abelian.DoldKan.equivalence (A := C)).counitIso.app K.complex).hom ≫ K.π
  quasiIso := by
    have := K.quasiIso
    have : QuasiIso
        ((CategoryTheory.Abelian.DoldKan.equivalence (A := C)).counitIso.app K.complex).hom :=
      quasiIso_of_isIso _
    have h : QuasiIso (((CategoryTheory.Abelian.DoldKan.equivalence (A := C)).counitIso.app
        K.complex).hom ≫ K.π) := quasiIso_comp _ _
    exact quasiIso_comp (hφ' := h) _ _

/-- An object with a projective resolution has a simplicial projective resolution. -/
instance [HasProjectiveResolution X] : Nonempty (SimplicialProjectiveResolution X) :=
  ⟨ofProjectiveResolution (projectiveResolution X)⟩

/-! ### Simplicial derived functors -/

section Derived

variable {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D)

/-- The complex `s(F(P))` computing the simplicial left derived functors of `F` at `X`: the
alternating face map complex of the simplicial object obtained by applying `F` termwise to a
simplicial projective resolution `P` of `X`. -/
abbrev derivedComplex (P : SimplicialProjectiveResolution X) : ChainComplex D ℕ :=
  (alternatingFaceMapComplex D).obj (P.obj ⋙ F)

/-- The morphism `s(F(P)) ⟶ s(F(Q))` induced by a morphism `f : P ⟶ Q` of simplicial objects. -/
abbrev derivedComplexMap (f : P.obj ⟶ Q.obj) : P.derivedComplex F ⟶ Q.derivedComplex F :=
  (alternatingFaceMapComplex D).map (Functor.whiskerRight f F)

/-- The identity induces the identity. -/
@[simp]
lemma derivedComplexMap_id : derivedComplexMap F (𝟙 P.obj) = 𝟙 _ := by
  simp [derivedComplexMap]

/-- The construction `f ↦ s(F(f))` is compatible with composition. -/
@[simp, reassoc]
lemma derivedComplexMap_comp (f : P.obj ⟶ Q.obj) (f' : Q.obj ⟶ S.obj) :
    derivedComplexMap F (f ≫ f') = derivedComplexMap F f ≫ derivedComplexMap F f' := by
  unfold derivedComplexMap
  rw [Functor.whiskerRight_comp]
  exact Functor.map_comp _ _ _

/-- For any functor `F`, a lift `f : P ⟶ Q` of the identity of `X` induces a homotopy
equivalence `s(F(P)) ⟶ s(F(Q))` of chain complexes: `F` preserves simplicial homotopies, and the
alternating face map complex carries them to chain homotopies. -/
theorem IsLift.homotopyEquivalences_derivedComplexMap {P Q : SimplicialProjectiveResolution X}
    {f : P.obj ⟶ Q.obj} (hf : IsLift P Q (𝟙 X) f) :
    HomologicalComplex.homotopyEquivalences D (ComplexShape.down ℕ) (derivedComplexMap F f) :=
  homotopyEquivalences_alternatingFaceMapComplex_map
    (SimplicialObject.homotopyEquivalences_whiskerRight F hf.homotopyEquivalences)

variable [CategoryWithHomology D]

/-- The `i`-th simplicial left derived object `LᵢF(X) = Hᵢ(s(F(P)))`, computed from a
simplicial projective resolution `P` of `X`. -/
abbrev derivedHomology (P : SimplicialProjectiveResolution X) (i : ℕ) : D :=
  (P.derivedComplex F).homology i

/-- Two lifts of the same morphism induce the same morphism on derived objects: they are
simplicially homotopic, `F` preserves simplicial homotopies, and simplicially homotopic maps
induce chain homotopic maps of alternating face map complexes. -/
theorem IsLift.homologyMap_derivedComplexMap_eq {g : X ⟶ Y} {f f' : P.obj ⟶ Q.obj}
    (hf : IsLift P Q g f) (hf' : IsLift P Q g f') (i : ℕ) :
    HomologicalComplex.homologyMap (derivedComplexMap F f) i =
      HomologicalComplex.homologyMap (derivedComplexMap F f') i := by
  obtain ⟨H⟩ := hf.nonempty_homotopy hf'
  exact (H.whiskerRight F).map_homology_eq i

/-- The morphism `LᵢF(X) ⟶ LᵢF(Y)` induced by `g : X ⟶ Y`, computed with simplicial projective
resolutions `P` of `X` and `Q` of `Y`: the map on homology of any lift of `g`. -/
def derivedMap (g : X ⟶ Y) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (i : ℕ) :
    P.derivedHomology F i ⟶ Q.derivedHomology F i :=
  HomologicalComplex.homologyMap (derivedComplexMap F (exists_isLift P Q g).choose) i

/-- `derivedMap F g P Q i` is induced by any lift of `g`. -/
theorem IsLift.derivedMap_eq {g : X ⟶ Y} {f : P.obj ⟶ Q.obj} (hf : IsLift P Q g f) (i : ℕ) :
    derivedMap F g P Q i = HomologicalComplex.homologyMap (derivedComplexMap F f) i :=
  (exists_isLift P Q g).choose_spec.homologyMap_derivedComplexMap_eq F hf i

/-- The identity of `X` induces the identity of `LᵢF(X)`. -/
@[simp]
theorem derivedMap_id (P : SimplicialProjectiveResolution X) (i : ℕ) :
    derivedMap F (𝟙 X) P P i = 𝟙 _ := by
  rw [(isLift_id P).derivedMap_eq, derivedComplexMap_id, HomologicalComplex.homologyMap_id]

/-- The maps induced on derived objects are compatible with composition. -/
@[reassoc (attr := simp)]
theorem derivedMap_comp (g : X ⟶ Y) (g' : Y ⟶ Z) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (S : SimplicialProjectiveResolution Z) (i : ℕ) :
    derivedMap F g P Q i ≫ derivedMap F g' Q S i = derivedMap F (g ≫ g') P S i := by
  rw [((exists_isLift P Q g).choose_spec.comp (exists_isLift Q S g').choose_spec).derivedMap_eq,
    derivedComplexMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- **Independence of the resolution.** The derived objects computed from two simplicial
projective resolutions of the same object are canonically isomorphic, by the map induced by any
lift of the identity. -/
@[simps]
def derivedIso (P Q : SimplicialProjectiveResolution X) (i : ℕ) :
    P.derivedHomology F i ≅ Q.derivedHomology F i where
  hom := derivedMap F (𝟙 X) P Q i
  inv := derivedMap F (𝟙 X) Q P i

/-- The comparison isomorphism of a resolution with itself is the identity. -/
@[simp]
theorem derivedIso_refl (P : SimplicialProjectiveResolution X) (i : ℕ) :
    derivedIso F P P i = Iso.refl _ := by
  ext
  simp

/-- The comparison isomorphisms are compatible with composition. -/
@[simp]
theorem derivedIso_trans (P Q S : SimplicialProjectiveResolution X) (i : ℕ) :
    derivedIso F P Q i ≪≫ derivedIso F Q S i = derivedIso F P S i := by
  ext
  simp

/-- The comparison isomorphisms are natural in the object resolved. -/
@[reassoc]
theorem derivedMap_comp_derivedIso_hom (g : X ⟶ Y) (P : SimplicialProjectiveResolution X)
    (Q Q' : SimplicialProjectiveResolution Y) (i : ℕ) :
    derivedMap F g P Q i ≫ (derivedIso F Q Q' i).hom = derivedMap F g P Q' i := by
  simp

/-- The comparison isomorphisms are natural in the object resolved. -/
@[reassoc]
theorem derivedIso_hom_comp_derivedMap (g : X ⟶ Y) (P P' : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (i : ℕ) :
    (derivedIso F P P' i).hom ≫ derivedMap F g P' Q i = derivedMap F g P Q i := by
  simp

end Derived

/-! ### The derived object in degree zero -/

section Zero

/-- The augmentation coequalizes the two faces `d₀, d₁ : P₁ ⟶ P₀`. -/
lemma δ_zero_comp_ε (P : SimplicialProjectiveResolution X) :
    P.obj.δ 0 ≫ P.ε = P.obj.δ 1 ≫ P.ε := by
  have h := P.π.comm 1 0
  simp only [HomologicalComplex.single_obj_d, comp_zero] at h
  rw [← sub_eq_zero, ← Preadditive.sub_comp, ← alternatingFaceMapComplex_obj_d_one_zero]
  exact h.symm

/-- The augmentation vanishes on the image of the first differential of the Moore complex. -/
lemma d_one_zero_comp_ε (P : SimplicialProjectiveResolution X) :
    ((alternatingFaceMapComplex C).obj P.obj).d 1 0 ≫ P.ε = 0 :=
  (P.π.comm 1 0).symm.trans (by simp only [HomologicalComplex.single_obj_d]; exact comp_zero)

/-- The augmentation of a simplicial projective resolution presents `X` as the cokernel of
`d₀ - d₁ : P₁ ⟶ P₀`: the sequence `P₁ → P₀ → X` is exact and `ε` is an epimorphism. -/
theorem exact_ε (P : SimplicialProjectiveResolution X) :
    (ShortComplex.mk _ _ P.d_one_zero_comp_ε).Exact ∧ Epi P.ε := by
  have h := (ChainComplex.quasiIsoAt₀_iff P.π).1 inferInstance
  rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by rfl) (by rfl)] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  exact h1

variable {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D)

/-- The first differential of `s(F(P))` is `F(d₀) - F(d₁)`. -/
lemma derivedComplex_d_one_zero (P : SimplicialProjectiveResolution X) :
    (P.derivedComplex F).d 1 0 = F.map (P.obj.δ 0) - F.map (P.obj.δ 1) :=
  alternatingFaceMapComplex_obj_d_one_zero (P.obj ⋙ F)

/-- `F(ε)` vanishes on the image of the first differential of `s(F(P))`. -/
lemma derivedComplex_d_one_zero_comp_map_ε (P : SimplicialProjectiveResolution X) :
    (P.derivedComplex F).d 1 0 ≫ F.map P.ε = 0 := by
  rw [derivedComplex_d_one_zero, Preadditive.sub_comp, ← F.map_comp, ← F.map_comp,
    δ_zero_comp_ε, sub_self]

/-- The morphism `s(F(P)) ⟶ F(X)[0]` induced by `F` applied to the augmentation. -/
def derivedComplexπ (P : SimplicialProjectiveResolution X) :
    P.derivedComplex F ⟶ (ChainComplex.single₀ D).obj (F.obj X) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨F.map P.ε, derivedComplex_d_one_zero_comp_map_ε F P⟩

/-- In degree `0` the morphism `derivedComplexπ F P` is `F(ε)`. -/
@[simp]
lemma derivedComplexπ_f_zero (P : SimplicialProjectiveResolution X) :
    (P.derivedComplexπ F).f 0 = F.map P.ε :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The morphisms `derivedComplexπ` are compatible with lifts. -/
lemma derivedComplexMap_comp_derivedComplexπ {g : X ⟶ Y} {f : P.obj ⟶ Q.obj}
    (hf : IsLift P Q g f) :
    derivedComplexMap F f ≫ Q.derivedComplexπ F =
      P.derivedComplexπ F ≫ (ChainComplex.single₀ D).map (F.map g) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [isLift_iff] at hf
  simp only [HomologicalComplex.comp_f, derivedComplexπ_f_zero, ChainComplex.single₀_map_f_zero]
  simp only [derivedComplexMap, alternatingFaceMapComplex_map_f, Functor.whiskerRight_app]
  exact (F.map_comp _ _).symm.trans ((congrArg F.map hf).trans (F.map_comp _ _))

/-- `F` *is right exact on `P`* when `F(P₁) ⇉ F(P₀) → F(X)` is a cokernel sequence for the
differential `F(d₀) - F(d₁)`: the sequence `F(P₁) → F(P₀) → F(X)` is exact and `F(ε)` is an
epimorphism. For a functor preserving reflexive coequalizers this holds for every simplicial
projective resolution, since `P₁ ⇉ P₀ → X` is a reflexive coequalizer. -/
def IsRightExactOn (P : SimplicialProjectiveResolution X) : Prop :=
  (ShortComplex.mk _ _ (derivedComplex_d_one_zero_comp_map_ε F P)).Exact ∧ Epi (F.map P.ε)

/-- If `F` is right exact on `P`, then `s(F(P)) ⟶ F(X)[0]` is a quasi-isomorphism in degree
`0`. -/
lemma quasiIsoAt_derivedComplexπ_zero {P : SimplicialProjectiveResolution X}
    (hP : IsRightExactOn F P) : QuasiIsoAt (P.derivedComplexπ F) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by rfl) (by rfl)]
  simp only [IsRightExactOn] at hP
  simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, derivedComplexπ_f_zero]
  exact hP

/-- **The derived object in degree zero.** If `F` is right exact on `P`, then
`L₀F(X) = H₀(s(F(P)))` is identified with `F(X)` through `F(ε)`. -/
def derivedHomologyZeroIso {P : SimplicialProjectiveResolution X} (hP : IsRightExactOn F P) :
    P.derivedHomology F 0 ≅ F.obj X :=
  have := quasiIsoAt_derivedComplexπ_zero F hP
  isoOfQuasiIsoAt (P.derivedComplexπ F) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

/-- The identification `L₀F(X) ≅ F(X)` is natural. -/
@[reassoc]
theorem derivedMap_comp_derivedHomologyZeroIso_hom (g : X ⟶ Y)
    {P : SimplicialProjectiveResolution X} {Q : SimplicialProjectiveResolution Y}
    (hP : IsRightExactOn F P) (hQ : IsRightExactOn F Q) :
    derivedMap F g P Q 0 ≫ (derivedHomologyZeroIso F hQ).hom =
      (derivedHomologyZeroIso F hP).hom ≫ F.map g := by
  have := quasiIsoAt_derivedComplexπ_zero F hP
  have := quasiIsoAt_derivedComplexπ_zero F hQ
  obtain ⟨f, hf⟩ := exists_isLift P Q g
  rw [derivedHomologyZeroIso, derivedHomologyZeroIso]
  simp only [Iso.trans_hom, isoOfQuasiIsoAt_hom, hf.derivedMap_eq,
    ← HomologicalComplex.homologyMap_comp_assoc, derivedComplexMap_comp_derivedComplexπ F hf,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality]

end Zero

end SimplicialProjectiveResolution

section Functor

variable [HasProjectiveResolutions C] {D : Type u'} [Category.{v'} D] [Preadditive D]
  [CategoryWithHomology D] (F : C ⥤ D)

/-- The `i`-th *simplicial left derived functor* `LᵢF : C ⥤ D` of an arbitrary (not necessarily
additive) functor `F : C ⥤ D`, in the sense of Dold–Puppe: `LᵢF(X) = Hᵢ(s(F(P)))` for a chosen
simplicial projective resolution `P` of `X`, and `LᵢF(g)` is induced by any lift of `g`. By
`Stacks.simplicialLeftDerivedObjIso` any other simplicial projective resolution computes it. -/
def simplicialLeftDerived (i : ℕ) : C ⥤ D where
  obj X := (Classical.arbitrary (SimplicialProjectiveResolution X)).derivedHomology F i
  map g := SimplicialProjectiveResolution.derivedMap F g _ _ i
  map_id _ := SimplicialProjectiveResolution.derivedMap_id F _ i
  map_comp g g' := (SimplicialProjectiveResolution.derivedMap_comp F g g' _ _ _ i).symm

/-- The value of the simplicial left derived functor is computed by any simplicial projective
resolution. -/
def simplicialLeftDerivedObjIso {X : C} (P : SimplicialProjectiveResolution X) (i : ℕ) :
    (simplicialLeftDerived F i).obj X ≅ P.derivedHomology F i :=
  SimplicialProjectiveResolution.derivedIso F _ P i

/-- Under the identifications `simplicialLeftDerivedObjIso`, the simplicial left derived functor
acts on morphisms by the map induced by any lift. -/
@[reassoc]
theorem simplicialLeftDerived_map_comp_objIso_hom {X Y : C} (g : X ⟶ Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (i : ℕ) :
    (simplicialLeftDerived F i).map g ≫ (simplicialLeftDerivedObjIso F Q i).hom =
      (simplicialLeftDerivedObjIso F P i).hom ≫
        SimplicialProjectiveResolution.derivedMap F g P Q i := by
  simp [simplicialLeftDerived, simplicialLeftDerivedObjIso]

end Functor

/-! ### Exterior powers of modules -/

namespace SimplicialProjectiveResolution

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R}

/-- The exterior power functors are right exact on every simplicial projective resolution of a
module: `⋀ⁿ P₁ ⇉ ⋀ⁿ P₀ → ⋀ⁿ M` is a coequalizer, by
`exteriorPower.range_map_sub_map_eq_ker_map` applied to the reflexive pair `d₀, d₁` with common
section `s₀`. -/
theorem isRightExactOn_exteriorPower (P : SimplicialProjectiveResolution M) (n : ℕ) :
    IsRightExactOn (ModuleCat.exteriorPower.functor R n) P := by
  obtain ⟨hex, hepi⟩ := P.exact_ε
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  rw [ModuleCat.epi_iff_surjective] at hepi
  have hd : (((alternatingFaceMapComplex _).obj P.obj).d 1 0).hom =
      (P.obj.δ 0).hom - (P.obj.δ 1).hom := by
    rw [alternatingFaceMapComplex_obj_d_one_zero]
    rfl
  refine ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have := exteriorPower.range_map_sub_map_eq_ker_map hepi (hd ▸ hex)
      (fun y => ⟨P.obj.σ 0 y, ?_, ?_⟩) n
    · show LinearMap.range
          ((P.derivedComplex (ModuleCat.exteriorPower.functor R n)).d 1 0).hom =
        LinearMap.ker ((ModuleCat.exteriorPower.functor R n).map P.ε).hom
      rw [derivedComplex_d_one_zero]
      exact this
    · exact ConcreteCategory.congr_hom (P.obj.δ_comp_σ_self' (i := 0) rfl) y
    · exact ConcreteCategory.congr_hom (P.obj.δ_comp_σ_succ' (i := 0) rfl) y
  · rw [ModuleCat.epi_iff_surjective]
    exact exteriorPower.map_surjective hepi

/-- **Existence of free simplicial resolutions.** Every module `M` has a simplicial projective
resolution whose terms are free modules: the Dold–Kan functor `Γ` applied to a free resolution
of `M`, whose terms are finite direct sums of free modules. -/
theorem exists_free (M : ModuleCat.{u} R) :
    ∃ P : SimplicialProjectiveResolution M, ∀ n, Module.Free R (P.obj _⦋n⦌) := by
  classical
  obtain ⟨D, hD, hFree⟩ := exists_free_resolution R M
  refine ⟨ofProjectiveResolution
    (CochainComplex.KFlat.freeProjectiveResolution D hD hFree), fun n => ?_⟩
  have : ∀ i, Module.Free R (DoldKan.Γ₀.Obj.summand (C := ModuleCat.{u} R)
      (CochainComplex.KFlat.freeProjectiveResolution D hD hFree).complex (op ⦋n⦌) i) :=
    fun i => hFree _
  exact Module.Free.of_equiv (ModuleCat.coprodIsoDirectSum _).symm.toLinearEquiv

end SimplicialProjectiveResolution

/-! ### The derived functors of the exterior square -/

namespace DerivedSquare

variable (R : Type u) [CommRing R]

/-- The exterior square functor `M ↦ ⋀² M` on `R`-modules. -/
abbrev exteriorSquare : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ModuleCat.exteriorPower.functor R 2

variable {R} {M N : ModuleCat.{u} R}

/-- The complex `LΛ²(P)`: the alternating face map complex of the simplicial module obtained by
applying `⋀²` termwise to a simplicial projective resolution `P` of `M`. -/
abbrev complex (P : SimplicialProjectiveResolution M) : ChainComplex (ModuleCat.{u} R) ℕ :=
  P.derivedComplex (exteriorSquare R)

/-- The derived exterior square `LᵢΛ²(M) = Hᵢ(LΛ²(P))`, computed from a simplicial projective
resolution `P` of `M`. Any two resolutions give canonically isomorphic modules,
`SimplicialProjectiveResolution.derivedIso`, and a module map induces maps between them,
`SimplicialProjectiveResolution.derivedMap`. -/
abbrev homology (P : SimplicialProjectiveResolution M) (i : ℕ) : ModuleCat.{u} R :=
  P.derivedHomology (exteriorSquare R) i

/-- **`L₀Λ²(M) ≅ ⋀² M`**, through `⋀²` of the augmentation `P₀ ⟶ M`. -/
def homologyZeroIso (P : SimplicialProjectiveResolution M) :
    homology P 0 ≅ M.exteriorPower 2 :=
  SimplicialProjectiveResolution.derivedHomologyZeroIso _ (P.isRightExactOn_exteriorPower 2)

/-- The identification `L₀Λ²(M) ≅ ⋀² M` is natural in `M`. -/
@[reassoc]
theorem derivedMap_comp_homologyZeroIso_hom (g : M ⟶ N) (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution N) :
    SimplicialProjectiveResolution.derivedMap (exteriorSquare R) g P Q 0 ≫
        (homologyZeroIso Q).hom =
      (homologyZeroIso P).hom ≫ ModuleCat.exteriorPower.map g 2 :=
  SimplicialProjectiveResolution.derivedMap_comp_derivedHomologyZeroIso_hom _ g _ _

variable (R) in
/-- The `i`-th derived functor `LᵢΛ² : ModuleCat R ⥤ ModuleCat R` of the exterior square, in
the sense of Dold–Puppe. -/
abbrev functor (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  simplicialLeftDerived (exteriorSquare R) i

variable (R) in
/-- **`L₀Λ² ≅ Λ²`** as functors. -/
def functorZeroIso : functor R 0 ≅ exteriorSquare R :=
  NatIso.ofComponents (fun _ => homologyZeroIso (Classical.arbitrary _)) fun g =>
    derivedMap_comp_homologyZeroIso_hom g _ _

end DerivedSquare

end Stacks

/-! ### Comparison of derived objects along a change of categories -/

namespace Stacks

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {D : Type*} [Category D] [Abelian D] {D' : Type*} [Category D'] [Abelian D']
  {F : C ⥤ D} {F' : C' ⥤ D'} {G : C ⥤ C'} {H : D ⥤ D'} [H.Additive] [H.PreservesHomology]

/-- **Comparison of derived objects along a change of categories.** Let `e : F ⋙ H ≅ G ⋙ F'`
for functors `F : C ⥤ D`, `F' : C' ⥤ D'`, `G : C ⥤ C'` and `H : D ⥤ D'` with `H` additive and
preserving homology. For a simplicial object `K` of `C`, `H` carries the homology of the Moore
complex `s(F(K))` to that of `s(F'(G(K)))`. -/
def derivedHomologyMapIso (e : F ⋙ H ≅ G ⋙ F') (K : SimplicialObject C) (i : ℕ) :
    H.obj (((alternatingFaceMapComplex D).obj (K ⋙ F)).homology i) ≅
      ((alternatingFaceMapComplex D').obj ((K ⋙ G) ⋙ F')).homology i :=
  (((alternatingFaceMapComplex D).obj (K ⋙ F)).mapHomologyIso H i).symm ≪≫
    HomologicalComplex.homologyMapIso ((alternatingFaceMapComplexCompIso (K ⋙ F) H).symm ≪≫
      (alternatingFaceMapComplex D').mapIso
        (Functor.isoWhiskerLeft K e ≪≫ (Functor.associator K G F').symm)) i

/-- The comparison `derivedHomologyMapIso`, as a composite. -/
lemma derivedHomologyMapIso_hom (e : F ⋙ H ≅ G ⋙ F') (K : SimplicialObject C) (i : ℕ) :
    (derivedHomologyMapIso e K i).hom =
      (((alternatingFaceMapComplex D).obj (K ⋙ F)).mapHomologyIso H i).inv ≫
        HomologicalComplex.homologyMap ((alternatingFaceMapComplexCompIso (K ⋙ F) H).inv ≫
          (alternatingFaceMapComplex D').map
            (Functor.whiskerLeft K e.hom ≫ (Functor.associator K G F').inv)) i := rfl

/-- The comparison `derivedHomologyMapIso` is natural in the simplicial object. -/
@[reassoc]
theorem map_homologyMap_comp_derivedHomologyMapIso_hom (e : F ⋙ H ≅ G ⋙ F')
    {K K' : SimplicialObject C} (f : K ⟶ K') (i : ℕ) :
    H.map (HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex D).map (Functor.whiskerRight f F)) i) ≫
        (derivedHomologyMapIso e K' i).hom =
      (derivedHomologyMapIso e K i).hom ≫ HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex D').map
          (Functor.whiskerRight (Functor.whiskerRight f G) F')) i := by
  rw [derivedHomologyMapIso_hom, derivedHomologyMapIso_hom,
    HomologicalComplex.map_homologyMap_comp_mapHomologyIso_inv_assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  ext n
  simpa using e.hom.naturality (f.app (op ⦋n⦌))

section Paste

variable {C'' : Type*} [Category C''] {D'' : Type*} [Category D''] [Abelian D'']
  {F'' : C'' ⥤ D''} {G₁ : C ⥤ C'} {G₂ : C' ⥤ C''} {H₁ : D ⥤ D'} {H₂ : D' ⥤ D''}

/-- The pasting of two squares of functors `F ⋙ H₁ ≅ G₁ ⋙ F'` and `F' ⋙ H₂ ≅ G₂ ⋙ F''`. -/
def pasteIso (e₁ : F ⋙ H₁ ≅ G₁ ⋙ F') (e₂ : F' ⋙ H₂ ≅ G₂ ⋙ F'') :
    F ⋙ H₁ ⋙ H₂ ≅ (G₁ ⋙ G₂) ⋙ F'' :=
  (Functor.associator F H₁ H₂).symm ≪≫ Functor.isoWhiskerRight e₁ H₂ ≪≫
    Functor.associator G₁ F' H₂ ≪≫ Functor.isoWhiskerLeft G₁ e₂ ≪≫
      (Functor.associator G₁ G₂ F'').symm

omit [Abelian D] [Abelian D'] [Abelian D''] in
/-- The components of a pasted square. -/
@[simp]
lemma pasteIso_hom_app (e₁ : F ⋙ H₁ ≅ G₁ ⋙ F') (e₂ : F' ⋙ H₂ ≅ G₂ ⋙ F'') (X : C) :
    (pasteIso e₁ e₂).hom.app X = H₂.map (e₁.hom.app X) ≫ e₂.hom.app (G₁.obj X) := by
  simp [pasteIso]

variable [H₁.Additive] [H₂.Additive] [H₁.PreservesHomology] [H₂.PreservesHomology]

/-- **Transitivity of the comparison.** The comparison along a pasted square is the composite
of the comparisons along the two squares. -/
theorem derivedHomologyMapIso_pasteIso_hom (e₁ : F ⋙ H₁ ≅ G₁ ⋙ F')
    (e₂ : F' ⋙ H₂ ≅ G₂ ⋙ F'') (K : SimplicialObject C) (i : ℕ) :
    (derivedHomologyMapIso (pasteIso e₁ e₂) K i).hom =
      H₂.map (derivedHomologyMapIso e₁ K i).hom ≫ (derivedHomologyMapIso e₂ (K ⋙ G₁) i).hom := by
  rw [derivedHomologyMapIso_hom, derivedHomologyMapIso_hom, derivedHomologyMapIso_hom,
    HomologicalComplex.mapHomologyIso_comp_inv, H₂.map_comp]
  simp only [Category.assoc]
  rw [HomologicalComplex.map_homologyMap_comp_mapHomologyIso_inv_assoc,
    ← HomologicalComplex.homologyMap_comp]
  refine congrArg (fun φ => _ ≫ _ ≫ HomologicalComplex.homologyMap φ i) ?_
  ext n
  simp

end Paste

section Transport

variable {G' : C ⥤ C'} {H' : D ⥤ D'} [H'.Additive] [H'.PreservesHomology]

/-- **Naturality of the comparison in the square.** Natural transformations `α : G ⟶ G'` and
`β : H ⟶ H'` compatible with squares `e : F ⋙ H ≅ G ⋙ F'` and `e' : F ⋙ H' ≅ G' ⋙ F'` are
compatible with the comparisons. -/
theorem app_comp_derivedHomologyMapIso_hom (e : F ⋙ H ≅ G ⋙ F') (e' : F ⋙ H' ≅ G' ⋙ F')
    (α : G ⟶ G') (β : H ⟶ H')
    (h : Functor.whiskerLeft F β ≫ e'.hom = e.hom ≫ Functor.whiskerRight α F')
    (K : SimplicialObject C) (i : ℕ) :
    β.app _ ≫ (derivedHomologyMapIso e' K i).hom =
      (derivedHomologyMapIso e K i).hom ≫ HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex D').map
          (Functor.whiskerRight (Functor.whiskerLeft K α) F')) i := by
  rw [derivedHomologyMapIso_hom, derivedHomologyMapIso_hom,
    HomologicalComplex.app_comp_mapHomologyIso_inv_assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  ext n
  simpa using NatTrans.congr_app h (K.obj (op ⦋n⦌))

end Transport

/-- The comparison along the trivial square `F ⋙ 𝟭 ≅ 𝟭 ⋙ F` is the identity. -/
@[simp]
theorem derivedHomologyMapIso_refl_hom (K : SimplicialObject C) (i : ℕ) :
    (derivedHomologyMapIso (F.rightUnitor ≪≫ F.leftUnitor.symm) K i).hom = 𝟙 _ := by
  have h : (alternatingFaceMapComplexCompIso (K ⋙ F) (𝟭 D)).inv ≫
      (alternatingFaceMapComplex D).map
        (Functor.whiskerLeft K (F.rightUnitor ≪≫ F.leftUnitor.symm).hom ≫
          (Functor.associator K (𝟭 C) F).inv) = 𝟙 _ := by
    ext n
    simp
  rw [derivedHomologyMapIso_hom, HomologicalComplex.mapHomologyIso_id_inv, h,
    HomologicalComplex.homologyMap_id, Category.comp_id]

/-! ### Images of simplicial projective resolutions -/

namespace SimplicialProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {C' : Type u'} [Category.{v'} C'] [Abelian C']
  (G : C ⥤ C') [G.Additive] {X Y : C}

/-- The image under an additive functor `G` of the augmentation of a simplicial projective
resolution `P`, as a morphism from the Moore complex of `G(P)` to `G(X)` in degree `0`. -/
def mapπ (P : SimplicialProjectiveResolution X) :
    (alternatingFaceMapComplex C').obj (P.obj ⋙ G) ⟶ (ChainComplex.single₀ C').obj (G.obj X) :=
  (alternatingFaceMapComplexCompIso P.obj G).hom ≫ (G.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex G _ 0).hom.app X

/-- In degree `0`, the image of the augmentation is the image of `ε`. -/
@[simp]
lemma mapπ_f_zero (P : SimplicialProjectiveResolution X) : (P.mapπ G).f 0 = G.map P.ε := by
  simp [mapπ, ε]

/-- The image of a simplicial projective resolution `P` of `X` under an additive functor `G`,
when it is a simplicial projective resolution of `G(X)`: the terms `G(Pₙ)` are projective and the
image of the augmentation is a quasi-isomorphism. -/
@[simps! obj π]
def mapOfQuasiIso (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G)) :
    SimplicialProjectiveResolution (G.obj X) where
  obj := P.obj ⋙ G
  projective := hP
  π := P.mapπ G
  quasiIso := hπ

/-- The augmentation `P₀ ⟶ X` of the image of a resolution is the image of the augmentation. -/
@[simp]
lemma mapOfQuasiIso_ε (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G)) :
    (P.mapOfQuasiIso G hP hπ).ε = G.map P.ε :=
  mapπ_f_zero G P

/-- A functor preserving homology carries the augmentation to a quasi-isomorphism. -/
instance quasiIso_mapπ [G.PreservesHomology] (P : SimplicialProjectiveResolution X) :
    QuasiIso (P.mapπ G) := by
  unfold mapπ
  infer_instance

/-- The image of a simplicial projective resolution under an additive functor preserving
homology and projective objects (for instance an exact left adjoint whose right adjoint preserves
epimorphisms). -/
abbrev map [G.PreservesHomology] [G.PreservesProjectiveObjects]
    (P : SimplicialProjectiveResolution X) : SimplicialProjectiveResolution (G.obj X) :=
  P.mapOfQuasiIso G (fun n => G.projective_obj (P.obj _⦋n⦌)) inferInstance

variable {G} {P : SimplicialProjectiveResolution X} {Q : SimplicialProjectiveResolution Y}

/-- A morphism between images of resolutions lies over `g` exactly when it is compatible with the
images of the augmentations in degree `0`. -/
private lemma isLift_mapOfQuasiIso_iff {C₂ : Type*} [Category C₂] [Abelian C₂] {Y : C₂}
    {Q : SimplicialProjectiveResolution Y} {G' : C₂ ⥤ C'} [G'.Additive] {g : G.obj X ⟶ G'.obj Y}
    {f : P.obj ⋙ G ⟶ Q.obj ⋙ G'} {hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))}
    {hπ : QuasiIso (P.mapπ G)} {hQ : ∀ n, Projective (G'.obj (Q.obj _⦋n⦌))}
    {hπ' : QuasiIso (Q.mapπ G')} :
    IsLift (P.mapOfQuasiIso G hP hπ) (Q.mapOfQuasiIso G' hQ hπ') g f ↔
      f.app (op ⦋0⦌) ≫ G'.map Q.ε = G.map P.ε ≫ g :=
  (isLift_iff _ _).trans (by rw [mapOfQuasiIso_ε, mapOfQuasiIso_ε]; rfl)

/-- The image of a lift of `g` is a lift of the image of `g`. -/
lemma IsLift.mapOfQuasiIso {g : X ⟶ Y} {f : P.obj ⟶ Q.obj} (hf : IsLift P Q g f)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hQ : ∀ n, Projective (G.obj (Q.obj _⦋n⦌))) (hπ' : QuasiIso (Q.mapπ G)) :
    IsLift (P.mapOfQuasiIso G hP hπ) (Q.mapOfQuasiIso G hQ hπ') (G.map g)
      (Functor.whiskerRight f G) := by
  rw [isLift_iff] at hf
  refine isLift_mapOfQuasiIso_iff.2 ?_
  simpa only [Functor.whiskerRight_app, Functor.map_comp] using congrArg G.map hf

/-- A natural transformation `α : G ⟶ G'` induces a lift of `α_X` between the images of a
resolution of `X`. -/
lemma isLift_whiskerLeft {G' : C ⥤ C'} [G'.Additive] (α : G ⟶ G')
    (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hP' : ∀ n, Projective (G'.obj (P.obj _⦋n⦌))) (hπ' : QuasiIso (P.mapπ G')) :
    IsLift (P.mapOfQuasiIso G hP hπ) (P.mapOfQuasiIso G' hP' hπ') (α.app X)
      (Functor.whiskerLeft P.obj α) := by
  exact isLift_mapOfQuasiIso_iff.2 (α.naturality P.ε).symm

variable {D : Type*} [Category D] [Abelian D] {D' : Type*} [Category D'] [Abelian D']
  {F : C ⥤ D} {F' : C' ⥤ D'} {H : D ⥤ D'} [H.Additive] [H.PreservesHomology]

/-- **Comparison of derived objects along a change of categories.** For
`e : F ⋙ H ≅ G ⋙ F'` with `H` additive and preserving homology, and a simplicial projective
resolution `P` of `X` whose image under `G` is a simplicial projective resolution of `G(X)`,
`H(LᵢF(X)) ≅ LᵢF'(G(X))`, both sides computed with these resolutions. -/
def mapDerivedHomologyIso (e : F ⋙ H ≅ G ⋙ F') (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G)) (i : ℕ) :
    H.obj (P.derivedHomology F i) ≅ (P.mapOfQuasiIso G hP hπ).derivedHomology F' i :=
  derivedHomologyMapIso e P.obj i

/-- **Naturality of the comparison of derived objects.** For `e : F ⋙ H ≅ G ⋙ F'` and a
morphism `g : X ⟶ Y`, the comparisons `H(LᵢF(X)) ≅ LᵢF'(G(X))` and `H(LᵢF(Y)) ≅ LᵢF'(G(Y))`
commute with the maps induced by `g` and by `G(g)`. -/
@[reassoc]
theorem map_derivedMap_comp_mapDerivedHomologyIso_hom (e : F ⋙ H ≅ G ⋙ F') (g : X ⟶ Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hQ : ∀ n, Projective (G.obj (Q.obj _⦋n⦌))) (hπ' : QuasiIso (Q.mapπ G)) (i : ℕ) :
    H.map (derivedMap F g P Q i) ≫ (mapDerivedHomologyIso e Q hQ hπ' i).hom =
      (mapDerivedHomologyIso e P hP hπ i).hom ≫
        derivedMap F' (G.map g) (P.mapOfQuasiIso G hP hπ) (Q.mapOfQuasiIso G hQ hπ') i := by
  obtain ⟨f, hf⟩ := exists_isLift P Q g
  rw [hf.derivedMap_eq, (hf.mapOfQuasiIso hP hπ hQ hπ').derivedMap_eq]
  exact map_homologyMap_comp_derivedHomologyMapIso_hom e f i

/-- **Naturality of the comparison in the square.** Natural transformations `α : G ⟶ G'` and
`β : H ⟶ H'` compatible with `e : F ⋙ H ≅ G ⋙ F'` and `e' : F ⋙ H' ≅ G' ⋙ F'` intertwine the
comparisons, through the map `LᵢF'(G(X)) ⟶ LᵢF'(G'(X))` induced by `α_X`. -/
@[reassoc]
theorem app_comp_mapDerivedHomologyIso_hom {G' : C ⥤ C'} [G'.Additive] {H' : D ⥤ D'}
    [H'.Additive] [H'.PreservesHomology] (e : F ⋙ H ≅ G ⋙ F') (e' : F ⋙ H' ≅ G' ⋙ F')
    (α : G ⟶ G') (β : H ⟶ H')
    (h : Functor.whiskerLeft F β ≫ e'.hom = e.hom ≫ Functor.whiskerRight α F')
    (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hP' : ∀ n, Projective (G'.obj (P.obj _⦋n⦌))) (hπ' : QuasiIso (P.mapπ G')) (i : ℕ) :
    β.app _ ≫ (mapDerivedHomologyIso e' P hP' hπ' i).hom =
      (mapDerivedHomologyIso e P hP hπ i).hom ≫
        derivedMap F' (α.app X) (P.mapOfQuasiIso G hP hπ) (P.mapOfQuasiIso G' hP' hπ') i := by
  rw [(isLift_whiskerLeft α P hP hπ hP' hπ').derivedMap_eq]
  exact app_comp_derivedHomologyMapIso_hom e e' α β h P.obj i

/-- The images of a resolution under `G₁ ⋙ G₂` and under `G₁` then `G₂` have the same
simplicial object, and the identity is a lift of the identity between them. -/
lemma isLift_mapOfQuasiIso_comp {C'' : Type*} [Category C''] [Abelian C''] {G₁ : C ⥤ C'}
    {G₂ : C' ⥤ C''} [G₁.Additive] [G₂.Additive] (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective ((G₁ ⋙ G₂).obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ (G₁ ⋙ G₂)))
    (hP₁ : ∀ n, Projective (G₁.obj (P.obj _⦋n⦌))) (hπ₁ : QuasiIso (P.mapπ G₁))
    (hP₂ : ∀ n, Projective (G₂.obj ((P.mapOfQuasiIso G₁ hP₁ hπ₁).obj _⦋n⦌)))
    (hπ₂ : QuasiIso ((P.mapOfQuasiIso G₁ hP₁ hπ₁).mapπ G₂)) :
    IsLift (P.mapOfQuasiIso (G₁ ⋙ G₂) hP hπ)
      ((P.mapOfQuasiIso G₁ hP₁ hπ₁).mapOfQuasiIso G₂ hP₂ hπ₂) (𝟙 _) (𝟙 (P.obj ⋙ G₁ ⋙ G₂)) := by
  refine isLift_mapOfQuasiIso_iff.2 ?_
  simp only [mapOfQuasiIso_ε]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **Transitivity of the comparison.** The comparison along a pasted square is the composite of
the comparisons along the two squares, up to the identification of the image of a resolution
under `G₁ ⋙ G₂` with its image under `G₁` then `G₂`. -/
theorem mapDerivedHomologyIso_pasteIso_hom {C'' : Type*} [Category C''] [Abelian C'']
    {D'' : Type*} [Category D''] [Abelian D''] {F'' : C'' ⥤ D''} {G₁ : C ⥤ C'}
    {G₂ : C' ⥤ C''} [G₁.Additive] [G₂.Additive] {H₁ : D ⥤ D'} {H₂ : D' ⥤ D''} [H₁.Additive]
    [H₂.Additive] [H₁.PreservesHomology] [H₂.PreservesHomology]
    (e₁ : F ⋙ H₁ ≅ G₁ ⋙ F') (e₂ : F' ⋙ H₂ ≅ G₂ ⋙ F'') (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective ((G₁ ⋙ G₂).obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ (G₁ ⋙ G₂)))
    (hP₁ : ∀ n, Projective (G₁.obj (P.obj _⦋n⦌))) (hπ₁ : QuasiIso (P.mapπ G₁))
    (hP₂ : ∀ n, Projective (G₂.obj ((P.mapOfQuasiIso G₁ hP₁ hπ₁).obj _⦋n⦌)))
    (hπ₂ : QuasiIso ((P.mapOfQuasiIso G₁ hP₁ hπ₁).mapπ G₂)) (i : ℕ) :
    (mapDerivedHomologyIso (pasteIso e₁ e₂) P hP hπ i).hom ≫
        (derivedIso F'' (P.mapOfQuasiIso (G₁ ⋙ G₂) hP hπ)
          ((P.mapOfQuasiIso G₁ hP₁ hπ₁).mapOfQuasiIso G₂ hP₂ hπ₂) i).hom =
      H₂.map (mapDerivedHomologyIso e₁ P hP₁ hπ₁ i).hom ≫
        (mapDerivedHomologyIso e₂ (P.mapOfQuasiIso G₁ hP₁ hπ₁) hP₂ hπ₂ i).hom := by
  rw [derivedIso_hom, (isLift_mapOfQuasiIso_comp P hP hπ hP₁ hπ₁ hP₂ hπ₂).derivedMap_eq]
  refine Eq.trans ?_ (derivedHomologyMapIso_pasteIso_hom e₁ e₂ P.obj i)
  refine (congrArg (fun φ => _ ≫ φ) ?_).trans (Category.comp_id _)
  exact (congrArg (fun φ => HomologicalComplex.homologyMap φ i)
    (derivedComplexMap_id F'' (P := P.mapOfQuasiIso (G₁ ⋙ G₂) hP hπ))).trans
      (HomologicalComplex.homologyMap_id _ _)

/-- The comparison along the trivial square `F ⋙ 𝟭 ≅ 𝟭 ⋙ F` is the identity. -/
theorem mapDerivedHomologyIso_refl_hom (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective ((𝟭 C).obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ (𝟭 C)))
    {F₀ : C ⥤ D} (i : ℕ) :
    (mapDerivedHomologyIso (F₀.rightUnitor ≪≫ F₀.leftUnitor.symm) P hP hπ i).hom ≫
        (derivedIso F₀ (P.mapOfQuasiIso (𝟭 C) hP hπ) P i).hom = 𝟙 _ := by
  have hl : IsLift (P.mapOfQuasiIso (𝟭 C) hP hπ) P (𝟙 ((𝟭 C).obj X)) (𝟙 P.obj) := by
    refine (isLift_iff _ _).2 ?_
    simp only [mapOfQuasiIso_ε]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  rw [derivedIso_hom, hl.derivedMap_eq]
  refine Eq.trans ?_ (derivedHomologyMapIso_refl_hom (F := F₀) P.obj i)
  refine (congrArg (fun φ => _ ≫ φ) ?_).trans (Category.comp_id _)
  exact (congrArg (fun φ => HomologicalComplex.homologyMap φ i)
    (derivedComplexMap_id F₀ (P := P))).trans (HomologicalComplex.homologyMap_id _ _)

end SimplicialProjectiveResolution

end Stacks
