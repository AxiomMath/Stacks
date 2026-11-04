module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Canonical structure maps of derived internal Hom

Let `R` be a commutative ring. The derived tensor--Hom adjunction on the unbounded derived
category `D(R)` fixes, once and for all, a derived tensor bifunctor `- ⊗ᴸ -`, a derived
internal-Hom bifunctor `RHom(-, -)`, and an additive equivalence
`Hom(K, RHom(L, M)) ≃+ Hom(K ⊗ᴸ L, M)`. This module builds from that adjunction, and from its
currying isomorphism, the four canonical structure maps of the internal-Hom formalism --
evaluation, coevaluation, composition, and the tensor--Hom diagonal -- and proves that
composition and the diagonal are functorial in each of their three variables.

## Main definitions

* `DerivedInternalHom.Model.adjunction`: the fixed derived tensor--Hom adjunction on `D(R)`.
* `DerivedInternalHom.Model.tensor`, `DerivedInternalHom.Model.hom`: its derived tensor and
  derived internal-Hom bifunctors, the latter contravariant in its first argument.
* `DerivedInternalHom.Model.homEquiv`: the additive adjunction bijection
  `Hom(K, RHom(L, M)) ≃+ Hom(K ⊗ᴸ L, M)`.
* `DerivedInternalHom.Model.curryingIso`: the currying isomorphism
  `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)`.
* `DerivedInternalHom.Model.evaluation`: the transpose `RHom(L, M) ⊗ᴸ L ⟶ M` of the identity
  of `RHom(L, M)`.
* `DerivedInternalHom.Model.coevaluation`: the transpose `K ⟶ RHom(L, K ⊗ᴸ L)` of the identity
  of `K ⊗ᴸ L`.
* `DerivedInternalHom.Model.composition`: the composition morphism
  `RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)`.
* `DerivedInternalHom.Model.diagonal`: the tensor--Hom diagonal
  `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)`.
* `DerivedInternalHom.Model.CanonicalMapLaws`: the six functoriality laws of composition and
  of the diagonal, bundled as a single proposition.

## Main results

* `DerivedInternalHom.Model.canonicalMapLaws`: composition is contravariantly natural in its
  source, dinatural in its middle object, and covariantly natural in its target; the diagonal
  is covariantly natural in the tensor factor and in the internal-Hom target, and
  contravariantly natural in the internal-Hom source.

## References

* [The Stacks Project, Section 15.74 (Tag 0A5W)](https://stacks.math.columbia.edu/tag/0A5W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace StacksDraft.DerivedHom

namespace DerivedInternalHom.Model

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat R)]

/-- The derived tensor--Hom adjunction fixed by the canonical K-flat/K-injective construction. -/
public abbrev adjunction (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat R)] : DerivedHomData R :=
  derivedHomAdjunction

/-- The derived tensor-product bifunctor on `D(R)`. -/
public abbrev tensor (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat R)] := (adjunction R).tensor

/-- The derived internal-Hom bifunctor on `D(R)`, contravariant in the first argument. -/
public abbrev hom (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat R)] := (adjunction R).hom

/-- The canonical derived tensor--Hom adjunction, additive and natural in all three variables. -/
public abbrev homEquiv (K L M : DerivedCategory (ModuleCat R)) :
    (K ⟶ (hom R).obj (Opposite.op L, M)) ≃+
      ((tensor R).obj (K, L) ⟶ M) :=
  (adjunction R).homEquiv K L M

/-- The canonical functorial currying isomorphism for derived internal Hom. -/
public abbrev curryingIso (K L M : DerivedCategory (ModuleCat R)) :
    (hom R).obj (Opposite.op K, (hom R).obj (Opposite.op L, M)) ≅
      (hom R).obj (Opposite.op ((tensor R).obj (K, L)), M) :=
  (derivedHomCurrying (R := R)).iso K L M

/-- Evaluation for derived internal Hom, obtained from the identity by the fixed adjunction. -/
public noncomputable def evaluation (L M : DerivedCategory (ModuleCat R)) :
    (tensor R).obj ((hom R).obj (Opposite.op L, M), L) ⟶ M :=
  homEquiv ((hom R).obj (Opposite.op L, M)) L M
    (𝟙 ((hom R).obj (Opposite.op L, M)))

/-- The transpose of the identity on a derived tensor product. -/
public noncomputable def coevaluation (K L : DerivedCategory (ModuleCat R)) :
    K ⟶ (hom R).obj (Opposite.op L, (tensor R).obj (K, L)) :=
  (homEquiv K L ((tensor R).obj (K, L))).symm
    (𝟙 ((tensor R).obj (K, L)))

/-- Composition of derived internal Homs `RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)`, the transpose
under the fixed adjunction of evaluation composed with the inverse currying isomorphism. -/
public noncomputable def composition (K L M : DerivedCategory (ModuleCat R)) :
    (tensor R).obj ((hom R).obj (Opposite.op L, M),
      (hom R).obj (Opposite.op K, L)) ⟶
        (hom R).obj (Opposite.op K, M) :=
  homEquiv ((hom R).obj (Opposite.op L, M))
      ((hom R).obj (Opposite.op K, L)) ((hom R).obj (Opposite.op K, M))
    ((hom R).map ((evaluation K L).op, 𝟙 M) ≫
      (curryingIso ((hom R).obj (Opposite.op K, L)) K M).inv)

/-- The tensor--Hom diagonal, obtained by tensoring coevaluation with the identity and then
composing internal Homs. -/
public noncomputable def diagonal (K L M : DerivedCategory (ModuleCat R)) :
    (tensor R).obj (K, (hom R).obj (Opposite.op M, L)) ⟶
      (hom R).obj (Opposite.op M, (tensor R).obj (K, L)) :=
  (tensor R).map (coevaluation K L, 𝟙 ((hom R).obj (Opposite.op M, L))) ≫
    composition M L ((tensor R).obj (K, L))

/-- Functoriality laws for the canonical composition and tensor--Hom diagonal. The equations
record ordinary naturality in covariant and contravariant variables and dinaturality in the
object occurring both as a source and a target of internal Hom. -/
public structure CanonicalMapLaws (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat R)] : Prop where
  /-- Contravariant naturality of composition in its source. -/
  composition_naturality_source
      {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) :
    (tensor R).map
          (𝟙 ((hom R).obj (Opposite.op L, M)), (hom R).map (f.op, 𝟙 L)) ≫
        composition K' L M =
      composition K L M ≫ (hom R).map (f.op, 𝟙 M)
  /-- Dinaturality of composition in its middle object. -/
  composition_dinaturality
      {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L) :
    (tensor R).map
          ((hom R).map (f.op, 𝟙 M), 𝟙 ((hom R).obj (Opposite.op K, L'))) ≫
        composition K L' M =
      (tensor R).map
          ((𝟙 ((hom R).obj (Opposite.op L, M)),
            ((hom R).map (𝟙 (Opposite.op K), f) :
              (hom R).obj (Opposite.op K, L') ⟶
                (hom R).obj (Opposite.op K, L))) :
            ((hom R).obj (Opposite.op L, M),
              (hom R).obj (Opposite.op K, L')) ⟶
            ((hom R).obj (Opposite.op L, M),
              (hom R).obj (Opposite.op K, L))) ≫
        composition K L M
  /-- Covariant naturality of composition in its target. -/
  composition_naturality_target
      {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M') :
    (tensor R).map
          ((hom R).map (𝟙 (Opposite.op L), f),
            𝟙 ((hom R).obj (Opposite.op K, L))) ≫
        composition K L M' =
      composition K L M ≫ (hom R).map (𝟙 (Opposite.op K), f)
  /-- Covariant naturality of the diagonal in the tensor factor. -/
  diagonal_naturality_tensor
      {K K' L M : DerivedCategory (ModuleCat R)} (f : K ⟶ K') :
    (tensor R).map (f, 𝟙 ((hom R).obj (Opposite.op M, L))) ≫
        diagonal K' L M =
      diagonal K L M ≫
        (hom R).map (𝟙 (Opposite.op M), (tensor R).map (f, 𝟙 L))
  /-- Covariant naturality of the diagonal in the internal-Hom target. -/
  diagonal_naturality_target
      {K L L' M : DerivedCategory (ModuleCat R)} (f : L ⟶ L') :
    (tensor R).map (𝟙 K, (hom R).map (𝟙 (Opposite.op M), f)) ≫
        diagonal K L' M =
      diagonal K L M ≫
        (hom R).map (𝟙 (Opposite.op M), (tensor R).map (𝟙 K, f))
  /-- Contravariant naturality of the diagonal in the internal-Hom source. -/
  diagonal_naturality_source
      {K L M M' : DerivedCategory (ModuleCat R)} (f : M' ⟶ M) :
    (tensor R).map (𝟙 K, (hom R).map (f.op, 𝟙 L)) ≫
        diagonal K L M' =
      diagonal K L M ≫
        (hom R).map (f.op, 𝟙 ((tensor R).obj (K, L)))

end DerivedInternalHom.Model

namespace DerivedInternalHom.Model

/-- If a square commutes for the forward maps of two isomorphisms, it commutes for the inverses. -/
private theorem inv_comp_eq_of_hom_comp_eq {C : Type*} [Category C] {X Y X' Y' : C}
    (e : X ≅ Y) (e' : X' ≅ Y') {a : X ⟶ X'} {b : Y ⟶ Y'}
    (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The inverse of the currying isomorphism `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)` is natural in
`K`. -/
public theorem currying_inv_naturality_left {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) :
    (hom R).map (((tensor R).map (f, 𝟙 L)).op, 𝟙 M) ≫
        (curryingIso K' L M).inv =
      (curryingIso K L M).inv ≫
        (hom R).map (f.op, 𝟙 ((hom R).obj (Opposite.op L, M))) := by
  exact inv_comp_eq_of_hom_comp_eq _ _ ((derivedHomCurrying (R := R)).naturality_left f)

/-- The inverse of the currying isomorphism `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)` is natural in
`L`. -/
public theorem currying_inv_naturality_middle {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L) :
    (hom R).map (((tensor R).map (𝟙 K, f)).op, 𝟙 M) ≫
        (curryingIso K L' M).inv =
      (curryingIso K L M).inv ≫
        (hom R).map (𝟙 (Opposite.op K), (hom R).map (f.op, 𝟙 M)) := by
  exact inv_comp_eq_of_hom_comp_eq _ _ ((derivedHomCurrying (R := R)).naturality_middle f)

/-- The inverse of the currying isomorphism `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)` is natural in
`M`. -/
public theorem currying_inv_naturality_right {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M') :
    (hom R).map (𝟙 (Opposite.op ((tensor R).obj (K, L))), f) ≫
        (curryingIso K L M').inv =
      (curryingIso K L M).inv ≫
        (hom R).map (𝟙 (Opposite.op K), (hom R).map (𝟙 (Opposite.op L), f)) := by
  exact inv_comp_eq_of_hom_comp_eq _ _ ((derivedHomCurrying (R := R)).naturality_right f)

/-- Composition `RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` of derived internal Homs is contravariantly
natural in its source `K`. -/
public theorem composition_naturality_source {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) :
    (tensor R).map
          (𝟙 ((hom R).obj (Opposite.op L, M)), (hom R).map (f.op, 𝟙 L)) ≫
        composition K' L M =
      composition K L M ≫ (hom R).map (f.op, 𝟙 M) := by
  unfold composition
  rw [← (adjunction R).homEquiv_dinaturality, ← (adjunction R).homEquiv_naturality_right]
  congr 1
  rw [Category.assoc, ← currying_inv_naturality_left, Category.assoc,
    ← currying_inv_naturality_middle]
  simp only [← Category.assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    ← op_comp, Category.comp_id]
  congr 2
  exact congrArg (fun e => (e.op, 𝟙 M))
    ((adjunction R).evaluation_naturality_left f)

/-- Composition `RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` of derived internal Homs is dinatural in
its middle object `L`. -/
public theorem composition_dinaturality {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L) :
    (tensor R).map
          ((hom R).map (f.op, 𝟙 M), 𝟙 ((hom R).obj (Opposite.op K, L'))) ≫
        composition K L' M =
      (tensor R).map
          ((𝟙 ((hom R).obj (Opposite.op L, M)),
            ((hom R).map (𝟙 (Opposite.op K), f) :
              (hom R).obj (Opposite.op K, L') ⟶
                (hom R).obj (Opposite.op K, L))) :
            ((hom R).obj (Opposite.op L, M),
              (hom R).obj (Opposite.op K, L')) ⟶
            ((hom R).obj (Opposite.op L, M),
              (hom R).obj (Opposite.op K, L))) ≫
        composition K L M := by
  unfold composition
  rw [← (adjunction R).homEquiv_naturality_left, ← (adjunction R).homEquiv_dinaturality]
  congr 1
  rw [Category.assoc, ← currying_inv_naturality_left]
  simp only [← Category.assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    ← op_comp, Category.comp_id]
  congr 2
  exact congrArg (fun e => (e.op, 𝟙 M))
    ((adjunction R).evaluation_naturality_right f).symm

/-- Composition `RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` of derived internal Homs is covariantly
natural in its target `M`. -/
public theorem composition_naturality_target {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M') :
    (tensor R).map
          ((hom R).map (𝟙 (Opposite.op L), f),
            𝟙 ((hom R).obj (Opposite.op K, L))) ≫
        composition K L M' =
      composition K L M ≫ (hom R).map (𝟙 (Opposite.op K), f) := by
  unfold composition
  rw [← (adjunction R).homEquiv_naturality_left, ← (adjunction R).homEquiv_naturality_right]
  congr 1
  rw [Category.assoc, ← currying_inv_naturality_right]
  simp only [← Category.assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp]

/-- Coevaluation `K ⟶ RHom(L, K ⊗ᴸ L)` is natural in `K`. -/
public theorem coevaluation_naturality_left {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K K' L : DerivedCategory (ModuleCat R)} (f : K ⟶ K') :
    f ≫ coevaluation K' L =
      coevaluation K L ≫ (hom R).map (𝟙 (Opposite.op L), (tensor R).map (f, 𝟙 L)) := by
  apply ((adjunction R).homEquiv K L _).injective
  rw [(adjunction R).homEquiv_naturality_left,
    (adjunction R).homEquiv_naturality_right]
  simp only [coevaluation, homEquiv, AddEquiv.apply_symm_apply,
    Category.comp_id, Category.id_comp]

/-- Coevaluation `K ⟶ RHom(L, K ⊗ᴸ L)` is dinatural in `L`. -/
public theorem coevaluation_dinaturality {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L L' : DerivedCategory (ModuleCat R)} (f : L ⟶ L') :
    coevaluation K L ≫ (hom R).map (𝟙 (Opposite.op L), (tensor R).map (𝟙 K, f)) =
      coevaluation K L' ≫ (hom R).map (show (Opposite.op L', (tensor R).obj (K, L')) ⟶
        (Opposite.op L, (tensor R).obj (K, L')) from
        (f.op, 𝟙 ((tensor R).obj (K, L')))) := by
  apply ((adjunction R).homEquiv K L _).injective
  rw [(adjunction R).homEquiv_naturality_right, (adjunction R).homEquiv_dinaturality]
  simp only [coevaluation, homEquiv, AddEquiv.apply_symm_apply,
    Category.comp_id, Category.id_comp]

/-- The tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is covariantly natural in the
tensor factor `K`. -/
public theorem diagonal_naturality_tensor {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K K' L M : DerivedCategory (ModuleCat R)} (f : K ⟶ K') :
    (tensor R).map (f, 𝟙 ((hom R).obj (Opposite.op M, L))) ≫
        diagonal K' L M =
      diagonal K L M ≫
        (hom R).map (𝟙 (Opposite.op M), (tensor R).map (f, 𝟙 L)) := by
  unfold diagonal
  rw [Category.assoc, ← composition_naturality_target]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp, Category.comp_id]
  rw [coevaluation_naturality_left f]

/-- The tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is covariantly natural in the
internal-Hom target `L`. -/
public theorem diagonal_naturality_target {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L L' M : DerivedCategory (ModuleCat R)} (f : L ⟶ L') :
    (tensor R).map (𝟙 K, (hom R).map (𝟙 (Opposite.op M), f)) ≫
        diagonal K L' M =
      diagonal K L M ≫
        (hom R).map (𝟙 (Opposite.op M), (tensor R).map (𝟙 K, f)) := by
  unfold diagonal
  rw [Category.assoc, ← composition_naturality_target]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.comp_id, Category.id_comp]
  rw [coevaluation_dinaturality f]
  simpa only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.comp_id, Category.id_comp] using
    congrArg ((tensor R).map (show
      (K, (hom R).obj (Opposite.op M, L)) ⟶
        ((hom R).obj (Opposite.op L', (tensor R).obj (K, L')),
          (hom R).obj (Opposite.op M, L)) from
      (coevaluation K L', 𝟙 ((hom R).obj (Opposite.op M, L)))) ≫ ·)
      (composition_dinaturality (K := M) (M := (tensor R).obj (K, L')) f).symm

/-- The tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is contravariantly natural in the
internal-Hom source `M`. -/
public theorem diagonal_naturality_source {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {K L M M' : DerivedCategory (ModuleCat R)} (f : M' ⟶ M) :
    (tensor R).map (𝟙 K, (hom R).map (f.op, 𝟙 L)) ≫
        diagonal K L M' =
      diagonal K L M ≫
        (hom R).map (f.op, 𝟙 ((tensor R).obj (K, L))) := by
  unfold diagonal
  rw [Category.assoc, ← composition_naturality_source]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.comp_id, Category.id_comp]

/-- The functoriality laws of the adjunction-defined composition and tensor--Hom diagonal. -/
public theorem canonicalMapLaws (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat R)] : CanonicalMapLaws R :=
  ⟨composition_naturality_source, composition_dinaturality,
    composition_naturality_target, diagonal_naturality_tensor,
    diagonal_naturality_target, diagonal_naturality_source⟩

end DerivedInternalHom.Model

end StacksDraft.DerivedHom

end
