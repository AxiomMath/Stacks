module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TransportedProjectionMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Base change squares transported along equivalences

Consider a square of categories

```
        Lf                      Lfe
   S  ------→  T          Se ------→ Te
   |           |          |          |
   | Lg        | Lg'      | Lge      | Lg'e
   v           v          v          v
   S' ------→  T'         Se' -----→ Te'
        Lf'                     Lf'e
```

together with equivalences `eS : Se ≌ S`, `eT : Te ≌ T`, `eS' : Se' ≌ S'`, `eT' : Te' ≌ T'`
and identifications `κ : e ⋙ L ≅ Le ⋙ e` of the four functors. This is the situation of the
étale derived categories `D(X_étale, Λ)`, read on the derived categories of the constant ringed
sites `(X_étale, Λ̲)` through `Stacks.EtaleCohomology.etaleDerivedEquivalence`. This file
transports three pieces of structure of the left square to the right one:

* an identification `θ : Lg ⋙ Lf' ≅ Lf ⋙ Lg'` of the two composites (`transportSquareIso`);
* the base change map `Stacks.CategoryTheory.BaseChange.map` of the square, for adjunctions
  transported by `Stacks.CategoryTheory.ProjectionMapTransport.transportedAdjunction`: the
  transported base change map is the original one read through the equivalences
  (`map_baseChangeMap_transportSquareIso`), hence one is invertible exactly when the other is;
* the compatibility `Stacks.AffineProjectionFormula.TensorComparisonCompatible` of four
  comparisons of tensor bifunctors around the square, for the comparisons transported by
  `TensorHomAdjunction.transportTensorIso` (`tensorComparisonCompatible_transportSquareIso`);

and, for one functor, the compatibility of a comparison of tensor bifunctors with commutativity
constraints (`transportTensorIso_braiding`).

Everything is stated with all functors as variables, so that an application to concrete derived
categories is a single instantiation.

## Main definitions

* `Stacks.CategoryTheory.ProjectionMapTransport.transportSquareIso`.

## Main results

* `Stacks.CategoryTheory.ProjectionMapTransport.map_transportSquareIso_hom_app`.
* `Stacks.CategoryTheory.ProjectionMapTransport.map_baseChangeMap_transportSquareIso`.
* `Stacks.CategoryTheory.ProjectionMapTransport.isIso_baseChangeMap_transportSquareIso_iff`.
* `Stacks.CategoryTheory.ProjectionMapTransport.tensorComparisonCompatible_transportSquareIso`.
* `Stacks.CategoryTheory.ProjectionMapTransport.transportTensorIso_braiding`.
-/

@[expose] public noncomputable section

namespace Stacks.CategoryTheory.ProjectionMapTransport

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.Prod
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

/-! ### The correspondence of comparisons of tensor bifunctors -/

section Tensor

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  (eC : C' ≌ C) (eD : D' ≌ D) {L : C ⥤ D} {L' : C' ⥤ D'}
  (κ : eC.functor ⋙ L ≅ L' ⋙ eD.functor)
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
  (μ : Functor.uncurry.obj TC ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj TD)

/-- **The transported comparison of tensor products, read through the equivalences**: the image
under `e_D` of the comparison `TensorHomAdjunction.transportTensorIso` is the original comparison,
conjugated by `κ` and by the counits of the equivalences. -/
theorem map_transportTensorIso_hom_app (a b : C') :
    eD.functor.map ((TensorHomAdjunction.transportTensorIso eD eC κ μ).hom.app (a, b)) =
      κ.inv.app ((Functor.uncurry.obj (TensorHomAdjunction.transportTensor eC TC)).obj (a, b)) ≫
        L.map ((transportTensorCompIso eC TC).hom.app (a, b)) ≫
          μ.hom.app (eC.functor.obj a, eC.functor.obj b) ≫
            (Functor.uncurry.obj TD).map (κ.hom.app a ×ₘ κ.hom.app b) ≫
              (transportTensorCompIso eD TD).inv.app (L'.obj a, L'.obj b) := by
  rw [← cancel_epi (κ.hom.app _), Iso.hom_inv_id_app_assoc]
  exact comparison_transportTensorIso eC eD κ μ a b

/-- The image under `e` of a transported bifunctor applied to two morphisms is the original
bifunctor applied to their images, conjugated by the counit of `e`. -/
theorem map_uncurry_transportTensor_map {E E' : Type*} [Category E] [Category E'] (e : E' ≌ E)
    (T : E ⥤ E ⥤ E) {a b a' b' : E'} (x : a ⟶ a') (y : b ⟶ b') :
    e.functor.map ((Functor.uncurry.obj (TensorHomAdjunction.transportTensor e T)).map
        (x ×ₘ y)) =
      (transportTensorCompIso e T).hom.app (a, b) ≫
        (Functor.uncurry.obj T).map (e.functor.map x ×ₘ e.functor.map y) ≫
          (transportTensorCompIso e T).inv.app (a', b') := by
  rw [← cancel_mono ((transportTensorCompIso e T).hom.app (a', b'))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  refine ((transportTensorCompIso e T).hom.naturality (x ×ₘ y)).trans ?_
  simp

/-- The component of `transportTensorCompIso` is the counit of the equivalence. -/
theorem transportTensorCompIso_hom_app (T : C ⥤ C ⥤ C) (a b : C') :
    (transportTensorCompIso eC T).hom.app (a, b) =
      eC.counit.app ((T.obj (eC.functor.obj a)).obj (eC.functor.obj b)) := by
  simp [transportTensorCompIso, TensorHomAdjunction.uncurryTransportTensorIso]

/-- The inverse component of `transportTensorCompIso` is the inverse of the counit. -/
theorem transportTensorCompIso_inv_app (T : C ⥤ C ⥤ C) (a b : C') :
    (transportTensorCompIso eC T).inv.app (a, b) =
      eC.counitInv.app ((T.obj (eC.functor.obj a)).obj (eC.functor.obj b)) := by
  simp [transportTensorCompIso, TensorHomAdjunction.uncurryTransportTensorIso]

/-- The image under `e` of `e⁻¹` of a morphism between values of a bifunctor, through
`transportTensorCompIso`. -/
theorem map_inverse_map_transportTensorCompIso (T : C ⥤ C ⥤ C) (a b a' b' : C')
    (β : (T.obj (eC.functor.obj a)).obj (eC.functor.obj b) ⟶
      (T.obj (eC.functor.obj a')).obj (eC.functor.obj b')) :
    eC.functor.map (eC.inverse.map β) =
      (transportTensorCompIso eC T).hom.app (a, b) ≫ β ≫
        (transportTensorCompIso eC T).inv.app (a', b') := by
  rw [transportTensorCompIso_hom_app, transportTensorCompIso_inv_app]
  exact Equivalence.fun_inv_map _ _ _ _

/-- The image under `e_D` of `L'` of a morphism is `L` of its image under `e_C`, conjugated by
`κ`. -/
theorem map_map_of_iso {x y : C'} (z : x ⟶ y) :
    eD.functor.map (L'.map z) = κ.inv.app x ≫ L.map (eC.functor.map z) ≫ κ.hom.app y := by
  rw [← cancel_epi (κ.hom.app x), Iso.hom_inv_id_app_assoc]
  exact (κ.hom.naturality z).symm

/-- A commutative constraint `b : T ⟶ T.flip` is natural in both variables, in uncurried form. -/
@[reassoc]
theorem uncurry_map_braiding (T : D ⥤ D ⥤ D) (b : T ⟶ T.flip) {x x' y y' : D}
    (u : x ⟶ x') (v : y ⟶ y') :
    (Functor.uncurry.obj T).map (u ×ₘ v) ≫ (b.app x').app y' =
      (b.app x).app y ≫ (Functor.uncurry.obj T).map (v ×ₘ u) := by
  have h1 := congrArg (fun τ => τ.app y) (b.naturality u)
  have h2 := (b.app x').naturality v
  simp only [NatTrans.comp_app, Functor.flip_obj_map, Functor.flip_map_app] at h1 h2
  simp only [Functor.uncurry_obj_map, Category.assoc, h2, reassoc_of% h1,
    (T.map v).naturality u]

variable (bC : TC ⟶ TC.flip) (bD : TD ⟶ TD.flip)

/-- **A comparison of tensor products compatible with commutativity constraints stays so after
transport.** If `L(A ⊗ B) ≅ LA ⊗ LB` carries the constraint `b_C` to `b_D`, then the transported
comparison carries the transported constraints `e⁻¹(b(e -, e -))` to each other. -/
theorem transportTensorIso_braiding
    (h : ∀ a b : C, L.map ((bC.app a).app b) ≫ μ.hom.app (b, a) =
      μ.hom.app (a, b) ≫ (bD.app (L.obj a)).app (L.obj b))
    (a b : C') :
    L'.map (eC.inverse.map ((bC.app (eC.functor.obj a)).app (eC.functor.obj b))) ≫
        (TensorHomAdjunction.transportTensorIso eD eC κ μ).hom.app (b, a) =
      (TensorHomAdjunction.transportTensorIso eD eC κ μ).hom.app (a, b) ≫
        eD.inverse.map ((bD.app (eD.functor.obj (L'.obj a))).app (eD.functor.obj (L'.obj b))) := by
  apply eD.functor.map_injective
  rw [Functor.map_comp, Functor.map_comp, map_map_of_iso eC eD κ,
    map_inverse_map_transportTensorCompIso eC TC a b b a, map_transportTensorIso_hom_app,
    map_transportTensorIso_hom_app,
    map_inverse_map_transportTensorCompIso eD TD (L'.obj a) (L'.obj b) (L'.obj b) (L'.obj a)]
  simp only [Functor.uncurry_obj_obj, TensorHomAdjunction.transportTensor_obj_obj,
    Functor.flip_obj_obj, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc L ((transportTensorCompIso eC TC).inv.app (b, a)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (h (eC.functor.obj a) (eC.functor.obj b))]
  exact congrArg (fun z => κ.inv.app _ ≫ L.map ((transportTensorCompIso eC TC).hom.app (a, b)) ≫
    μ.hom.app _ ≫ z) (uncurry_map_braiding_assoc TD bD (κ.hom.app a) (κ.hom.app b) _).symm

end Tensor

/-! ### Squares -/

section Square

variable {S T S' T' Se Te Se' Te' : Type*} [Category S] [Category T] [Category S']
  [Category T'] [Category Se] [Category Te] [Category Se'] [Category Te']
  (eS : Se ≌ S) (eT : Te ≌ T) (eS' : Se' ≌ S') (eT' : Te' ≌ T')
  {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'}
  {Lfe : Se ⥤ Te} {Lf'e : Se' ⥤ Te'} {Lge : Se ⥤ Se'} {Lg'e : Te ⥤ Te'}
  (κf : eS.functor ⋙ Lf ≅ Lfe ⋙ eT.functor) (κf' : eS'.functor ⋙ Lf' ≅ Lf'e ⋙ eT'.functor)
  (κg : eS.functor ⋙ Lg ≅ Lge ⋙ eS'.functor) (κg' : eT.functor ⋙ Lg' ≅ Lg'e ⋙ eT'.functor)
  (θ : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- The components of `transportSquareIso`, read in `T'`. -/
def transportSquareIsoApp (M : Se) :
    eT'.functor.obj (Lf'e.obj (Lge.obj M)) ≅ eT'.functor.obj (Lg'e.obj (Lfe.obj M)) :=
  κf'.symm.app (Lge.obj M) ≪≫ Lf'.mapIso (κg.symm.app M) ≪≫ θ.app (eS.functor.obj M) ≪≫
    Lg'.mapIso (κf.app M) ≪≫ κg'.app (Lfe.obj M)

/-- **The identification of the two composites around a square, transported along
equivalences**: `Lge ⋙ Lf'e ≅ Lfe ⋙ Lg'e`, the unique isomorphism whose image under `e_{T'}` is
`θ` conjugated by the four identifications `κ` (`map_transportSquareIso_hom_app`). -/
def transportSquareIso : Lge ⋙ Lf'e ≅ Lfe ⋙ Lg'e :=
  NatIso.ofComponents
    (fun M => eT'.fullyFaithfulFunctor.preimageIso
      (transportSquareIsoApp eS eT eS' eT' κf κf' κg κg' θ M))
    (fun {M N} u => by
      apply eT'.functor.map_injective
      simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
        transportSquareIsoApp, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
        Category.assoc]
      have h1 := κf'.inv.naturality (Lge.map u)
      have h2 := κg.inv.naturality u
      have h3 := θ.hom.naturality (eS.functor.map u)
      have h4 := κf.hom.naturality u
      have h5 := κg'.hom.naturality (Lfe.map u)
      simp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3 h4 h5
      rw [reassoc_of% h1, ← Lf'.map_comp_assoc, h2, Lf'.map_comp_assoc, reassoc_of% h3,
        ← Lg'.map_comp_assoc, h4, Lg'.map_comp_assoc, h5])

/-- The image of the transported identification under `e_{T'}`. -/
theorem map_transportSquareIso_hom_app (M : Se) :
    eT'.functor.map ((transportSquareIso eS eT eS' eT' κf κf' κg κg' θ).hom.app M) =
      κf'.inv.app (Lge.obj M) ≫ Lf'.map (κg.inv.app M) ≫ θ.hom.app (eS.functor.obj M) ≫
        Lg'.map (κf.hom.app M) ≫ κg'.hom.app (Lfe.obj M) := by
  simp [transportSquareIso, transportSquareIsoApp]

/-- Naturality of the identification of the two composites around a square, with `Lc` unfolded. -/
private theorem squareCompositeIso_naturality {Lc : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc) {X Y : S} (u : X ⟶ Y) :
    Lf'.map (Lg.map u) ≫ eg.hom.app Y ≫ ef.inv.app Y =
      eg.hom.app X ≫ ef.inv.app X ≫ Lg'.map (Lf.map u) := by
  have hθ := (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.naturality u
  simpa only [Functor.comp_obj, Functor.comp_map,
    Stacks.AffineProjectionFormula.squareCompositeIso_hom_app, Category.assoc] using hθ

section BaseChange

variable {Rf : T ⥤ S} {Rf' : T' ⥤ S'} {Rfe : Te ⥤ Se} {Rf'e : Te' ⥤ Se'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (ρf : Rfe ≅ eT.functor ⋙ Rf ⋙ eS.inverse) (ρf' : Rf'e ≅ eT'.functor ⋙ Rf' ⋙ eS'.inverse)
  {Lc : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The transported base change map is the original one, read through the equivalences.**
For adjunctions `Lf ⊣ Rf`, `Lf' ⊣ Rf'` transported along the equivalences
(`transportedAdjunction`) and the transported identification of the two composites
(`transportSquareIso`), the image under `e_{S'}` of the base change map
`Stacks.CategoryTheory.BaseChange.map` at `M` is the original base change map at `e_T M`,
conjugated by `κ_g`, `κ_{g'}` and the comparisons of the right adjoints. -/
theorem map_baseChangeMap_transportSquareIso (M : Te) :
    eS'.functor.map (Stacks.CategoryTheory.BaseChange.map
        (transportedAdjunction eS eT adjf κf ρf) (transportedAdjunction eS' eT' adjf' κf' ρf')
        (transportSquareIso eS eT eS' eT' κf κf' κg κg'
          (Stacks.AffineProjectionFormula.squareCompositeIso eg ef)) (Iso.refl _) M) =
      κg.inv.app (Rfe.obj M) ≫ Lg.map ((transportedPushforwardIso eS eT ρf).hom.app M) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (eT.functor.obj M) ≫
          Rf'.map (κg'.hom.app M) ≫
            (transportedPushforwardIso eS' eT' ρf').inv.app (Lg'e.obj M) := by
  have key : κf'.hom.app (Lge.obj (Rfe.obj M)) ≫ eT'.functor.map
      ((transportSquareIso eS eT eS' eT' κf κf' κg κg'
          (Stacks.AffineProjectionFormula.squareCompositeIso eg ef)).hom.app (Rfe.obj M) ≫
        (Iso.refl (Lfe ⋙ Lg'e)).inv.app (Rfe.obj M) ≫
          Lg'e.map ((transportedAdjunction eS eT adjf κf ρf).counit.app M)) =
      Lf'.map (κg.inv.app (Rfe.obj M) ≫ Lg.map ((transportedPushforwardIso eS eT ρf).hom.app M)) ≫
        ((eg.hom.app (Rf.obj (eT.functor.obj M)) ≫ ef.inv.app (Rf.obj (eT.functor.obj M)) ≫
          Lg'.map (adjf.counit.app (eT.functor.obj M))) ≫ κg'.hom.app M) := by
    rw [Iso.refl_inv, NatTrans.id_app, Category.id_comp, Functor.map_comp,
      map_transportSquareIso_hom_app, map_map_of_iso eT eT' κg',
      Stacks.AffineProjectionFormula.squareCompositeIso_hom_app]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
    rw [← Lg'.map_comp_assoc, counit_transportedAdjunction eS eT adjf κf ρf M, Lg'.map_comp_assoc,
      reassoc_of% (squareCompositeIso_naturality eg ef
        ((transportedPushforwardIso eS eT ρf).hom.app M))]
    rfl
  rw [Stacks.CategoryTheory.BaseChange.map_eq, map_homEquiv_transportedAdjunction,
    Stacks.CategoryTheory.BaseChange.map_eq, key, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  rfl

/-- **The transported base change map is invertible exactly when the original one is.** -/
theorem isIso_baseChangeMap_transportSquareIso_iff (M : Te) :
    IsIso (Stacks.CategoryTheory.BaseChange.map
        (transportedAdjunction eS eT adjf κf ρf) (transportedAdjunction eS' eT' adjf' κf' ρf')
        (transportSquareIso eS eT eS' eT' κf κf' κg κg'
          (Stacks.AffineProjectionFormula.squareCompositeIso eg ef)) (Iso.refl _) M) ↔
      IsIso (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (eT.functor.obj M)) := by
  rw [← isIso_iff_of_reflects_iso _ eS'.functor, map_baseChangeMap_transportSquareIso]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

end BaseChange

section TensorSquare

variable {TS : S ⥤ S ⥤ S} {TT : T ⥤ T ⥤ T} {TS' : S' ⥤ S' ⥤ S'} {TT' : T' ⥤ T' ⥤ T'}
  (μf : Functor.uncurry.obj TS ⋙ Lf ≅ Lf.prod Lf ⋙ Functor.uncurry.obj TT)
  (μf' : Functor.uncurry.obj TS' ⋙ Lf' ≅ Lf'.prod Lf' ⋙ Functor.uncurry.obj TT')
  (μg : Functor.uncurry.obj TS ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj TS')
  (μg' : Functor.uncurry.obj TT ⋙ Lg' ≅ Lg'.prod Lg' ⋙ Functor.uncurry.obj TT')
  {Lc : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

omit [Category S] [Category T] [Category S'] [Category Se] [Category Te] [Category Se']
  [Category Te'] in
/-- Cancelling an isomorphism and its inverse in the middle of a composite. -/
theorem comp_hom_inv_cancel {P Q R W : T'} (a : P ⟶ Q) (b : Q ⟶ R) (b' : R ⟶ Q) (a' : Q ⟶ P)
    (x : P ⟶ W) (hb : b ≫ b' = 𝟙 _) (ha : a ≫ a' = 𝟙 _) : (a ≫ b) ≫ b' ≫ a' ≫ x = x := by
  rw [Category.assoc, reassoc_of% hb, reassoc_of% ha]

omit [Category S] [Category T] [Category S'] [Category Se] [Category Te] [Category Se']
  [Category Te'] in
/-- Splitting off the first two factors of a composite in both variables of a bifunctor. -/
theorem uncurry_map_comp_comp (B : T' ⥤ T' ⥤ T') {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ : T'}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (x : P₂ ⟶ P₃) (c : Q₀ ⟶ Q₁) (d : Q₁ ⟶ Q₂) (y : Q₂ ⟶ Q₃) :
    (Functor.uncurry.obj B).map ((a ≫ b ≫ x) ×ₘ (c ≫ d ≫ y)) =
      (Functor.uncurry.obj B).map ((a ≫ b) ×ₘ (c ≫ d)) ≫ (Functor.uncurry.obj B).map (x ×ₘ y) := by
  rw [← bifunctor_map_comp_both, Category.assoc, Category.assoc]

/-- **The compatibility of four comparisons of tensor bifunctors around a square survives
transport along equivalences.** If the comparisons `μ` of the left square satisfy
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` at `(e_S M, e_S N)` for the
identification `eg`, `ef` of the two composites, then the transported comparisons
(`TensorHomAdjunction.transportTensorIso`) satisfy it at `(M, N)` for the transported
identification `transportSquareIso`. -/
theorem tensorComparisonCompatible_transportSquareIso (M N : Se)
    (h : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom
      (eS.functor.obj M) (eS.functor.obj N)) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (transportSquareIso eS eT eS' eT' κf κf' κg κg'
        (Stacks.AffineProjectionFormula.squareCompositeIso eg ef)) (Iso.refl _)
      (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eS TS))
      (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eS' TS'))
      (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eT TT))
      (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eT' TT'))
      (TensorHomAdjunction.transportTensorIso eT eS κf μf).hom
      (TensorHomAdjunction.transportTensorIso eT' eS' κf' μf').hom
      (TensorHomAdjunction.transportTensorIso eS' eS κg μg).hom
      (TensorHomAdjunction.transportTensorIso eT' eT κg' μg').hom M N := by
  rw [Stacks.AffineProjectionFormula.TensorComparisonCompatible] at h ⊢
  simp only [Stacks.AffineProjectionFormula.squareCompositeIso_hom_app, Iso.refl_inv,
    NatTrans.id_app, Category.comp_id] at h ⊢
  apply eT'.functor.map_injective
  simp only [Functor.map_comp]
  rw [map_map_of_iso eS' eT' κf', map_transportTensorIso_hom_app eS eS' κg μg,
    map_transportTensorIso_hom_app eS' eT' κf' μf', map_uncurry_transportTensor_map eT' TT',
    map_map_of_iso eT eT' κg', map_transportTensorIso_hom_app eS eT κf μf,
    map_transportTensorIso_hom_app eT eT' κg' μg']
  simp only [map_transportSquareIso_hom_app,
    Stacks.AffineProjectionFormula.squareCompositeIso_hom_app]
  simp only [Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← Lf'.map_comp_assoc ((transportTensorCompIso eS' TS').inv.app (Lge.obj M, Lge.obj N)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Lg'.map_comp_assoc (κf.hom.app _), Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp,
    ← Lg'.map_comp_assoc ((transportTensorCompIso eT TT).inv.app (Lfe.obj M, Lfe.obj N)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (bifunctor_comparison_naturality (Functor.uncurry.obj TS')
      (Functor.uncurry.obj TT') μf'.hom (κg.hom.app M) (κg.hom.app N)),
    ← Functor.map_comp_assoc (Functor.uncurry.obj TT'),
    ← Functor.map_comp_assoc (Functor.uncurry.obj TT'), prod_comp, prod_comp,
    reassoc_of% (bifunctor_comparison_naturality (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μg'.hom (κf.hom.app M) (κf.hom.app N)),
    ← Functor.map_comp_assoc (Functor.uncurry.obj TT'), prod_comp]
  dsimp only
  rw [comp_hom_inv_cancel (Lf'.map (κg.hom.app M)) (κf'.hom.app (Lge.obj M))
      (κf'.inv.app (Lge.obj M)) (Lf'.map (κg.inv.app M)) _ (κf'.hom_inv_id_app _) (by simp),
    comp_hom_inv_cancel (Lf'.map (κg.hom.app N)) (κf'.hom.app (Lge.obj N))
      (κf'.inv.app (Lge.obj N)) (Lf'.map (κg.inv.app N)) _ (κf'.hom_inv_id_app _) (by simp)]
  rw [uncurry_map_comp_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  exact congrArg (fun z => κf'.inv.app _ ≫ Lf'.map (κg.inv.app _) ≫ z)
    ((reassoc_of% squareCompositeIso_naturality eg ef
      ((transportTensorCompIso eS TS).hom.app (M, N))) _)

end TensorSquare

end Square

end Stacks.CategoryTheory.ProjectionMapTransport

end
