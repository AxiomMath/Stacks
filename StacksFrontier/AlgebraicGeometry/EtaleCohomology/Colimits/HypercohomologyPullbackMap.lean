module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryShiftedHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap

/-!
# Étale hypercohomology and its pull back maps

Let `X` be a scheme and `K` an object of the derived category `D(X_étale)` of abelian sheaves on
the small étale site of `X`. Its étale (hyper)cohomology in degree `p ∈ ℤ` is
`H^p(X, K) = Hom_{D(X_étale)}(ℤ, K[p])`, with `ℤ` the constant sheaf placed in degree zero. For a
single sheaf `F` placed in degree zero this is the étale cohomology `H^p(X, F)` (Mathlib's
`CategoryTheory.Sheaf.H`, an `Ext`-group out of `ℤ`).

Let `f : X ⟶ Y` be a morphism of schemes. Inverse image `f⁻¹` is exact, so it acts on derived
categories; for a complex `K` on `Y`, a complex `L` on `X` and a map of complexes
`κ : f⁻¹K ⟶ L` this gives the pull back map `H^p(Y, K) ⟶ H^p(X, L)`, which on a sheaf in degree
zero is the pull back map of étale cohomology `Stacks.EtaleCohomology.etaleCohomologyPullback`.

This file constructs the pull back maps and proves the properties a system of hypercohomology
groups and its long exact sequences need: pull back along a composite, naturality, the
compatibility with the connecting morphisms of short exact sequences of complexes, the
identification on a sheaf placed in degree zero, the shift of a sheaf placed in degree `n` to
degree `n + 1`, and the vanishing of `H^p(X, K)` for `p` below the degrees of `K`.

## Main definitions

* `Stacks.EtaleCohomology.etaleHypercohomology`: `H^p(X, K)` for `K ∈ D(X_étale)`.
* `Stacks.EtaleCohomology.etaleHypercohomologyMap`: the pull back map
  `H^p(Y, K) ⟶ H^p(X, L)` attached to `f : X ⟶ Y` and `κ : f⁻¹K ⟶ L` in `D(X_étale)`.
* `Stacks.EtaleCohomology.etaleHypercohomologyPullback`: the same for complexes `K`, `L` and a map
  of complexes `κ : f⁻¹K ⟶ L`.
* `Stacks.EtaleCohomology.etaleHypercohomologySingleAddEquiv`: `H^p(X, F[0]) ≃ H^p(X, F)` for
  `p ≥ 0` and a sheaf `F`.

## Main results

* `Stacks.EtaleCohomology.etaleHypercohomologyPullback_comp`: pull back along a composite.
* `Stacks.EtaleCohomology.etaleHypercohomologyPullback_comp_triangleOfSESδ`: compatibility with
  connecting morphisms.
* `Stacks.EtaleCohomology.etaleHypercohomologySingleAddEquiv_etaleCohomologyPullback`: on sheaves
  in degree zero the pull back map is the one of étale cohomology.
* `Stacks.EtaleCohomology.etaleHypercohomologyPullback_singleShiftAddEquiv`: compatibility with
  the identification `H^p(X, F[-n]) ≃ H^{p+1}(X, F[-n-1])`.
* `Stacks.EtaleCohomology.subsingleton_etaleHypercohomology_of_isStrictlyGE`: `H^p(X, K) = 0` if
  `K` vanishes in degrees `< n` and `p < n`.

## Implementation notes

The derived categories are the standard ones (`HasDerivedCategory.standard`), whose morphism
types live one universe above the abelian sheaves. The pull back map is
`CategoryTheory.Functor.mapAlongExact` along the exact functor `f⁻¹`, with the identification of
`f⁻¹ℤ` with `ℤ` of `Stacks.EtaleCohomology.smallEtalePullbackAbConstantIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Definitions -/

section Definitions

variable (X : Scheme.{u})

/-- The constant sheaf `ℤ` on the small étale site of `X` placed in degree zero. -/
abbrev etaleConstantComplex : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))

/-- **Étale hypercohomology** `H^p(X, K) = Hom_{D(X_étale)}(ℤ, K[p])` of an object `K` of the
derived category of abelian sheaves on the small étale site of `X`, for `p ∈ ℤ`. -/
abbrev etaleHypercohomology (K : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (p : ℤ) : Type (u + 2) :=
  ShiftedHom (DerivedCategory.Q.obj (etaleConstantComplex X)) K p

variable {X} {Y Z : Scheme.{u}}

/-- The identification of `ℤ[0]` on `X` with the inverse image along `f` of `ℤ[0]` on `Y`. -/
def etaleConstantComplexPullback (f : X ⟶ Y) :
    etaleConstantComplex X ⟶
      ((smallEtalePullbackAb f).mapHomologicalComplex _).obj (etaleConstantComplex Y) :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((smallEtalePullbackAbConstantIso f).inv.app (AddCommGrpCat.of (ULift ℤ))) ≫
    ((smallEtalePullbackAb f).mapCochainComplexSingleFunctor 0).inv.app _

/-- **The pull back map on étale hypercohomology.** For `f : X ⟶ Y`, objects `K` of
`D(Y_étale)` and `L` of `D(X_étale)` and a map `κ : f⁻¹K ⟶ L` in `D(X_étale)`, the map
`H^p(Y, K) ⟶ H^p(X, L)`: apply the derived inverse image, identify `f⁻¹ℤ` with `ℤ`, and compose
with `κ`. -/
def etaleHypercohomologyMap (f : X ⟶ Y)
    {K : DerivedCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1})}
    {L : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})}
    (κ : (smallEtalePullbackAb f).mapDerivedCategory.obj K ⟶ L) (p : ℤ) :
    etaleHypercohomology Y K p →+ etaleHypercohomology X L p :=
  ShiftedHom.mapAlongAddHom (smallEtalePullbackAb f).mapDerivedCategory
    (DerivedCategory.Q.map (etaleConstantComplexPullback f) ≫
      (smallEtalePullbackAb f).mapDerivedCategoryFactors.inv.app _) κ p

/-- **The pull back map on étale hypercohomology of complexes.** For `f : X ⟶ Y`, complexes `K`
on `Y` and `L` on `X` and a map of complexes `κ : f⁻¹K ⟶ L`, the map `H^p(Y, K) ⟶ H^p(X, L)`. -/
def etaleHypercohomologyPullback (f : X ⟶ Y)
    {K : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L) (p : ℤ) :
    etaleHypercohomology Y (DerivedCategory.Q.obj K) p →+
      etaleHypercohomology X (DerivedCategory.Q.obj L) p :=
  (smallEtalePullbackAb f).mapAlongExactAddHom (etaleConstantComplexPullback f) κ p

/-- The pull back map of complexes is `Functor.mapAlongExact` along `f⁻¹`, with the
identification `etaleConstantComplexPullback f` and `κ`. -/
lemma etaleHypercohomologyPullback_apply (f : X ⟶ Y)
    {K : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L) (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj K) p) :
    etaleHypercohomologyPullback f κ p x =
      (smallEtalePullbackAb f).mapAlongExact (etaleConstantComplexPullback f) κ x := rfl

/-- The pull back map of complexes is the pull back map of their images in the derived
category. -/
lemma etaleHypercohomologyPullback_eq_map (f : X ⟶ Y)
    {K : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L) (p : ℤ) :
    etaleHypercohomologyPullback f κ p =
      etaleHypercohomologyMap f ((smallEtalePullbackAb f).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map κ) p := rfl

end Definitions

/-! ### Pull back along a composite -/

section Composite

variable {X Y Z : Scheme.{u}}

/-- The identifications of `ℤ[0]` with its inverse images are compatible with composition. -/
lemma etaleConstantComplexPullback_comp (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z)
    (hgf : gf = g ≫ f) :
    etaleConstantComplexPullback g ≫
        ((smallEtalePullbackAb g).mapHomologicalComplex _).map (etaleConstantComplexPullback f) ≫
          (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' g f gf hgf)
            (ComplexShape.up ℤ)).hom.app _ =
      etaleConstantComplexPullback gf := by
  apply HomologicalComplex.from_single_hom_ext
  have hnat := (smallEtalePullbackAbComp' g f gf hgf).hom.naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))).inv
  simp only [Functor.comp_map] at hnat
  simp only [etaleConstantComplexPullback, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f,
    smallEtalePullbackAbConstantIso_comp_inv_app g f gf hgf, Category.assoc, Functor.map_comp]
  dsimp only [Functor.comp_obj]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc (smallEtalePullbackAb g),
    Iso.inv_hom_id, Functor.map_id, Category.id_comp, Category.comp_id, hnat]

/-- **Pull back along a composite.** Pulling back along `f` with `κ : f⁻¹K ⟶ L` and then along `g`
with `κ' : g⁻¹L ⟶ M` is pulling back along `gf = g ≫ f` with the composite
`(gf)⁻¹K ≅ g⁻¹f⁻¹K ⟶ g⁻¹L ⟶ M`. -/
lemma etaleHypercohomologyPullback_comp (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z)
    (hgf : gf = g ≫ f) {K : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ}
    {L : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {M : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L)
    (κ' : ((smallEtalePullbackAb g).mapHomologicalComplex _).obj L ⟶ M) (p : ℤ)
    (x : etaleHypercohomology Z (DerivedCategory.Q.obj K) p) :
    etaleHypercohomologyPullback g κ' p (etaleHypercohomologyPullback f κ p x) =
      etaleHypercohomologyPullback gf
        ((NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' g f gf hgf)
            (ComplexShape.up ℤ)).inv.app K ≫
          ((smallEtalePullbackAb g).mapHomologicalComplex _).map κ ≫ κ') p x := by
  simp only [etaleHypercohomologyPullback_apply]
  rw [Functor.mapAlongExact_mapAlongExact _ _ _ (smallEtalePullbackAbComp' g f gf hgf),
    etaleConstantComplexPullback_comp g f gf hgf]

end Composite

/-! ### Naturality and connecting morphisms -/

section Naturality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pulling back is natural in the target complex. -/
lemma etaleHypercohomologyPullback_comp_Q_map
    {K : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L L' : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L) (g : L ⟶ L') (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj K) p) :
    etaleHypercohomologyPullback f κ p x ≫ (DerivedCategory.Q.map g)⟦p⟧' =
      etaleHypercohomologyPullback f (κ ≫ g) p x :=
  Functor.mapAlongExact_comp_Q_map _ _ _ _ x

/-- Pulling back is natural in the source complex. -/
lemma etaleHypercohomologyPullback_Q_map
    {K K' : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ} (g : K ⟶ K')
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K' ⟶ L) (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj K) p) :
    etaleHypercohomologyPullback f κ p (x ≫ (DerivedCategory.Q.map g)⟦p⟧') =
      etaleHypercohomologyPullback f (((smallEtalePullbackAb f).mapHomologicalComplex _).map g ≫ κ)
        p x :=
  Functor.mapAlongExact_Q_map _ _ _ _ x

/-- **Pulling back commutes with the connecting morphisms** of short exact sequences of
complexes. -/
lemma etaleHypercohomologyPullback_comp_triangleOfSESδ
    {S : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ)}
    (hS : S.ShortExact)
    {S' : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (hS' : S'.ShortExact) (ψ : S.map ((smallEtalePullbackAb f).mapHomologicalComplex _) ⟶ S')
    {p q : ℤ} (h : 1 + p = q) (x : etaleHypercohomology Y (DerivedCategory.Q.obj S.X₃) p) :
    etaleHypercohomologyPullback f ψ.τ₁ q (x.comp (DerivedCategory.triangleOfSESδ hS) h) =
      (etaleHypercohomologyPullback f ψ.τ₃ p x).comp (DerivedCategory.triangleOfSESδ hS') h :=
  Functor.mapAlongExact_comp_triangleOfSESδ _ _ hS hS' ψ h x

/-- Pulling back commutes with a commuting square of maps of complexes. -/
private lemma etaleHypercohomologyPullback_comp_Q_map_eq
    {K K' : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ}
    {L L' : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (κ : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K ⟶ L)
    (κ' : ((smallEtalePullbackAb f).mapHomologicalComplex _).obj K' ⟶ L')
    (hκ : ((smallEtalePullbackAb f).mapHomologicalComplex _).map a ≫ κ' = κ ≫ b) (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj K) p) :
    etaleHypercohomologyPullback f κ p x ≫ (DerivedCategory.Q.map b)⟦p⟧' =
      etaleHypercohomologyPullback f κ' p (x ≫ (DerivedCategory.Q.map a)⟦p⟧') := by
  rw [etaleHypercohomologyPullback_comp_Q_map, etaleHypercohomologyPullback_Q_map, hκ]

/-- Pulling back commutes with the first map of a morphism of short complexes. -/
lemma etaleHypercohomologyPullback_comp_Q_map_f
    {S : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ)}
    {S' : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (ψ : S.map ((smallEtalePullbackAb f).mapHomologicalComplex _) ⟶ S') (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj S.X₁) p) :
    etaleHypercohomologyPullback f ψ.τ₁ p x ≫ (DerivedCategory.Q.map S'.f)⟦p⟧' =
      etaleHypercohomologyPullback f ψ.τ₂ p (x ≫ (DerivedCategory.Q.map S.f)⟦p⟧') := by
  exact etaleHypercohomologyPullback_comp_Q_map_eq f _ _ _ _ ψ.comm₁₂.symm p x

/-- Pulling back commutes with the second map of a morphism of short complexes. -/
lemma etaleHypercohomologyPullback_comp_Q_map_g
    {S : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ)}
    {S' : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (ψ : S.map ((smallEtalePullbackAb f).mapHomologicalComplex _) ⟶ S') (p : ℤ)
    (x : etaleHypercohomology Y (DerivedCategory.Q.obj S.X₂) p) :
    etaleHypercohomologyPullback f ψ.τ₂ p x ≫ (DerivedCategory.Q.map S'.g)⟦p⟧' =
      etaleHypercohomologyPullback f ψ.τ₃ p (x ≫ (DerivedCategory.Q.map S.g)⟦p⟧') := by
  exact etaleHypercohomologyPullback_comp_Q_map_eq f _ _ _ _ ψ.comm₂₃.symm p x

end Naturality

/-! ### Sheaves in degree zero -/

section Single

variable {X Y : Scheme.{u}}

/-- **Hypercohomology of a sheaf in degree zero is its étale cohomology.** -/
def etaleHypercohomologySingleAddEquiv (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1} F q ≃+ etaleHypercohomology X
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) q :=
  Ext.homAddEquiv

/-- `etaleHypercohomologySingleAddEquiv` sends a class in `H^q(X, F)` to its underlying morphism
of the derived category. -/
lemma etaleHypercohomologySingleAddEquiv_apply (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (q : ℕ) (x : Sheaf.H.{u + 1} F q) :
    etaleHypercohomologySingleAddEquiv F q x = x.hom := rfl

/-- **On sheaves in degree zero, the pull back map is the one of étale cohomology.** -/
lemma etaleHypercohomologySingleAddEquiv_etaleCohomologyPullback (f : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) (q : ℕ) (x : Sheaf.H.{u + 1} F q) :
    etaleHypercohomologySingleAddEquiv G q (etaleCohomologyPullback f φ q x) =
      etaleHypercohomologyPullback f
        (((smallEtalePullbackAb f).mapCochainComplexSingleFunctor 0).hom.app F ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) q
        (etaleHypercohomologySingleAddEquiv F q x) := by
  rw [etaleHypercohomologySingleAddEquiv_apply, etaleHypercohomologySingleAddEquiv_apply,
    etaleHypercohomologyPullback_apply, etaleCohomologyPullback_apply]
  exact (Functor.mapAlongExact_single_hom _ _ _ x).symm

/-- The identification `H^p(X, F[-n]) ≃ H^q(X, F[-m])` for `1 + n = m` and `1 + p = q`, from the
identification of complexes `F[-m]⟦1⟧ ≅ F[-n]`. -/
def etaleHypercohomologySingleShiftAddEquiv (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (n m : ℤ) (h : 1 + n = m) (p q : ℤ) (hpq : 1 + p = q) :
    etaleHypercohomology X
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F)) p ≃+
      etaleHypercohomology X
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) m).obj F)) q :=
  (AddEquiv.mk (Equiv.mk
      (fun x => x ≫ (DerivedCategory.Q.map
        (((CochainComplex.singleFunctors _).shiftIso 1 n m h).inv.app F))⟦p⟧')
      (fun y => y ≫ (DerivedCategory.Q.map
        (((CochainComplex.singleFunctors _).shiftIso 1 n m h).hom.app F))⟦p⟧')
      (fun x => by simp [← Functor.map_comp]) (fun y => by simp [← Functor.map_comp]))
      (fun x y => by simp)).trans
    (Functor.shiftedHomShiftAddEquiv _ _ p 1 q hpq)

/-- **Pulling back is compatible with `etaleHypercohomologySingleShiftAddEquiv`.** -/
lemma etaleHypercohomologyPullback_singleShiftAddEquiv (f : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) (n m : ℤ) (h : 1 + n = m) (p q : ℤ)
    (hpq : 1 + p = q)
    (x : etaleHypercohomology Y
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F)) p) :
    etaleHypercohomologySingleShiftAddEquiv G n m h p q hpq
        (etaleHypercohomologyPullback f
          (((smallEtalePullbackAb f).mapCochainComplexSingleFunctor n).hom.app F ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) n).map φ) p x) =
      etaleHypercohomologyPullback f
        (((smallEtalePullbackAb f).mapCochainComplexSingleFunctor m).hom.app F ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) m).map φ) q
        (etaleHypercohomologySingleShiftAddEquiv F n m h p q hpq x) := by
  have key := (smallEtalePullbackAb f).mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app
    φ n m h
  have hx : x = (x ≫ (DerivedCategory.Q.map
      (((CochainComplex.singleFunctors _).shiftIso 1 n m h).inv.app F))⟦p⟧') ≫
        (DerivedCategory.Q.map
          (((CochainComplex.singleFunctors _).shiftIso 1 n m h).hom.app F))⟦p⟧' := by
    have := ((shiftFunctor _ p).mapIso (DerivedCategory.Q.mapIso
      (((CochainComplex.singleFunctors _).shiftIso 1 n m h).app F))).inv_hom_id
    exact (Category.comp_id x).symm.trans ((congrArg (x ≫ ·) this).symm.trans
      (Category.assoc _ _ _).symm)
  show Functor.shiftedHomShiftAddEquiv _ _ p 1 q hpq
      (etaleHypercohomologyPullback f _ p x ≫ _) =
    etaleHypercohomologyPullback f _ q (Functor.shiftedHomShiftAddEquiv _ _ p 1 q hpq _)
  rw [etaleHypercohomologyPullback_comp_Q_map]
  conv_lhs => rw [hx, etaleHypercohomologyPullback_Q_map]
  rw [etaleHypercohomologyPullback_apply, etaleHypercohomologyPullback_apply,
    Functor.mapAlongExact_shiftedHomShiftAddEquiv]
  congr 2
  rw [← Category.assoc, key]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Functor.map_comp]
  rfl

end Single

/-! ### The long exact sequence -/

section LongExact

variable {X : Scheme.{u}}

/-- Composition with a morphism `g : K ⟶ L` of `D(X_étale)`, as the map
`H^p(X, K) ⟶ H^p(X, L)`. -/
def etaleHypercohomologyPostcomp {K L : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})}
    (g : K ⟶ L) (p : ℤ) : etaleHypercohomology X K p →+ etaleHypercohomology X L p :=
  Preadditive.rightComp _ (g⟦p⟧')

/-- `etaleHypercohomologyPostcomp g p` sends `x` to `x ≫ g⟦p⟧'`. -/
@[simp]
lemma etaleHypercohomologyPostcomp_apply
    {K L : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (g : K ⟶ L) (p : ℤ)
    (x : etaleHypercohomology X K p) : etaleHypercohomologyPostcomp g p x = x ≫ g⟦p⟧' := rfl

/-- Composition with an isomorphism `e : K ≅ L` of `D(X_étale)`, as the isomorphism
`H^p(X, K) ≃ H^p(X, L)`. -/
def etaleHypercohomologyPostcompAddEquiv
    {K L : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (e : K ≅ L) (p : ℤ) :
    etaleHypercohomology X K p ≃+ etaleHypercohomology X L p where
  toFun x := x ≫ e.hom⟦p⟧'
  invFun y := y ≫ e.inv⟦p⟧'
  left_inv x := by simp [← Functor.map_comp]
  right_inv y := by simp [← Functor.map_comp]
  map_add' x y := by simp

/-- `etaleHypercohomologyPostcompAddEquiv e p` sends `x` to `x ≫ e.hom⟦p⟧'`. -/
@[simp]
lemma etaleHypercohomologyPostcompAddEquiv_apply
    {K L : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (e : K ≅ L) (p : ℤ)
    (x : etaleHypercohomology X K p) :
    etaleHypercohomologyPostcompAddEquiv e p x = x ≫ e.hom⟦p⟧' := rfl

/-- The connecting map `H^p(X, K₃) ⟶ H^q(X, K₁)`, `1 + p = q`, of a short exact sequence of
complexes `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0`. -/
def etaleHypercohomologyδ
    {S : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (hS : S.ShortExact) (p q : ℤ) (h : 1 + p = q) :
    etaleHypercohomology X (DerivedCategory.Q.obj S.X₃) p →+
      etaleHypercohomology X (DerivedCategory.Q.obj S.X₁) q where
  toFun x := x.comp (DerivedCategory.triangleOfSESδ hS) h
  map_zero' := ShiftedHom.zero_comp _ _ _ _
  map_add' x y := ShiftedHom.add_comp _ _ _ _

/-- `etaleHypercohomologyδ hS p q h` sends `x` to its composite with the connecting morphism
`DerivedCategory.triangleOfSESδ hS`. -/
@[simp]
lemma etaleHypercohomologyδ_apply
    {S : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (hS : S.ShortExact) (p q : ℤ) (h : 1 + p = q)
    (x : etaleHypercohomology X (DerivedCategory.Q.obj S.X₃) p) :
    etaleHypercohomologyδ hS p q h x = x.comp (DerivedCategory.triangleOfSESδ hS) h := rfl

end LongExact

/-! ### Vanishing below the degrees of a complex -/

/-- **`H^p(X, K) = 0` for `p` below the degrees of `K`.** -/
lemma subsingleton_etaleHypercohomology_of_isStrictlyGE {X : Scheme.{u}}
    (K : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) (n p : ℤ)
    [K.IsStrictlyGE n] (hp : p < n) :
    Subsingleton (etaleHypercohomology X (DerivedCategory.Q.obj K) p) := by
  have : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.Q.obj K)⟦p⟧) (n - p) :=
    DerivedCategory.TStructure.t.isGE_shift _ n p (n - p) (by omega)
  have : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Q.obj (etaleConstantComplex X)) 0 :=
    (inferInstance : ((DerivedCategory.singleFunctor _ 0).obj _).IsLE 0)
  constructor
  intro x y
  rw [DerivedCategory.TStructure.t.zero x 0 (n - p) (by omega),
    DerivedCategory.TStructure.t.zero y 0 (n - p) (by omega)]

end Stacks.EtaleCohomology

end

