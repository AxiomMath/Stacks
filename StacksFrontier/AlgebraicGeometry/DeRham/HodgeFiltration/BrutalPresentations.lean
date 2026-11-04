module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Multiplicativity

/-!
# The two presentations of a brutal truncation agree

The library carries the brutal truncation `σ^{≥k}` of a cochain complex in two shapes, and uses
each in a different place.

* `CochainComplex.brutal` of `StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration` cuts out, in
  an `ℕ`-indexed complex, the subcomplex given by the subobjects `⊤` in degrees `≥ k` and `⊥`
  below. That is the shape in which the relative de Rham complex carries a wedge product, and
  `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge` of
  `StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Multiplicativity` — the multiplication
  `Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ σ^{≥(i + j)}Ω^•` of Stacks Section 0FM7 — is stated for it.
* Mathlib's `HomologicalComplex.stupidTrunc` along `ComplexShape.embeddingUpIntGE k`, applied to
  the `ℤ`-indexed extension by zero of the complex. That is the shape the Hodge filtration on
  hypercohomology is defined in: `AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian` and
  `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlus` of
  `StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic`, hence also the groups
  `H^n(X, σ^{≥p}Ω^•)` in which the Hodge-filtered first Chern class of Tag 0FME lives.

Nothing related the two, so the multiplication of Section 0FM7 could not be read in the
presentation the filtration on hypercohomology uses. This file relates them: extending a brutal
truncation by zero gives the stupid truncation of the extension, and an additive functor — in
particular the abelianisation that `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex`
applies to the de Rham complex — commutes with the brutal truncation. Both identifications lie
over the inclusions into the ambient complex, which is what makes them identifications of a *step
of the filtration* rather than of two complexes that happen to be isomorphic.

The reason both hold is the same degreewise computation: in degrees `≥ k` both sides are the term
of the ambient complex, the inclusion being an isomorphism there because the cutting subobject is
`⊤`; in lower degrees both sides vanish.

## Main definitions

* `CochainComplex.brutalExtendIso`: **`σ^{≥k}L^•` extended by zero is `stupidTrunc` of the
  extension**, for an `ℕ`-indexed complex `L^•`.
* `CochainComplex.mapBrutalIso`: **an additive functor commutes with the brutal truncation**,
  `F(σ^{≥k}L^•) ≅ σ^{≥k}F(L)^•`.
* `CochainComplex.mapBrutalExtendIso`: the two in succession, which is the form the de Rham
  complex needs.
* `AlgebraicGeometry.SheafOfModules.deRhamBrutalAbelianIso`: **the brutal truncation
  `σ^{≥k}Ω^•_{𝒪_X/A}` carrying the multiplication of Section 0FM7, read in abelian sheaves and
  extended by zero, is the truncation underlying
  `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlus`.**
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedgeAbelian`: **the multiplication
  `Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ σ^{≥(i + j)}Ω^•` of Section 0FM7 read in that presentation.**

## Main results

* `CochainComplex.mapBrutalExtendHom_ι` and
  `AlgebraicGeometry.SheafOfModules.deRhamBrutalAbelianIso_hom_ι`: the identifications lie over
  the inclusions into the ambient complex.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedgeAbelian_ι`: **composing the multiplication
  with the inclusion `σ^{≥(i + j)}Ω^• ⟶ Ω^•` of complexes of abelian sheaves returns the wedge
  product**, which is `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge_ιBrutal` in the
  realization in which the Hodge-filtered first Chern class lives.

## Where the cup products are

Section 0FM7 continues from the multiplication of complexes to cup products on *hypercohomology*
and to the two commutative squares used in Tag 0FME. For every natural pairing of hypercohomology
groups along multiplications of complexes, both squares are proved in
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup` and
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.gradedPieceMap_cup`
(`StacksFrontier/AlgebraicGeometry/DeRham/FirstChernClass/FilteredChernCupProduct.lean`), through the
identification of this file. The cup product of Cohomology, Section 0FKU is the natural pairing
`AlgebraicGeometry.SheafOfModules.truncationCupProduct`, built from the canonical global cup
product in `StacksFrontier/AlgebraicGeometry/DeRham/HodgeFiltration/CanonicalCupProduct.lean`, and
the squares for it are
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup` there
and `AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_hodgeFiltrationCup` in
`StacksFrontier/AlgebraicGeometry/DeRham/FirstChernClass/CanonicalChernCupProduct.lean`.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open HomologicalComplex StacksDraft.StupidTruncation

universe v u

namespace HomologicalComplex

/-- The extension by zero of an isomorphism of complexes is an isomorphism. -/
instance isIso_extendMap {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} {K L : HomologicalComplex C c}
    (φ : K ⟶ L) [IsIso φ] (e : c.Embedding c') : IsIso (extendMap φ e) where
  out := ⟨extendMap (inv φ) e, by
      rw [← extendMap_comp, IsIso.hom_inv_id, extendMap_id], by
      rw [← extendMap_comp, IsIso.inv_hom_id, extendMap_id]⟩

end HomologicalComplex

namespace StacksDraft.StupidTruncation

open HomologicalComplex ComplexShape

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

attribute [local instance] mono_ιStupidTrunc

/-- **The comparison of two stupid truncations is an isomorphism when the degrees between the two
indices carry nothing.** The map `σ^{≥b}K ⟶ σ^{≥a}K` of
`StacksDraft.StupidTruncation.stupidTruncGEMapLE`, for `a ≤ b`, differs from an isomorphism only
in the degrees `a ≤ n < b`, where the source vanishes and the target is `K^n`; if those terms of
`K` vanish too, it is invertible.

Two cases are used below: `a = b`, where the range is empty, and a complex concentrated in
degrees `≥ b`, where every term in the range vanishes. The second is what identifies
`σ^{≥p}Ω^•` for `p ≤ 0` with `σ^{≥0}Ω^•`, the de Rham complex having no negative terms. -/
lemma isIso_stupidTruncGEMapLE (K : CochainComplex C ℤ) {a b : ℤ} (h : a ≤ b)
    (hz : ∀ n : ℤ, a ≤ n → n < b → IsZero (K.X n)) :
    IsIso (stupidTruncGEMapLE K h) := by
  have hcomp : ∀ n : ℤ, IsIso ((stupidTruncGEMapLE K h).f n) := by
    intro n
    by_cases hn : b ≤ n
    · have : IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f n) :=
        isIso_ιStupidTrunc_f K _ (i := (n - a).toNat) (by
          show a + (((n - a).toNat : ℕ) : ℤ) = n
          omega)
      have : IsIso ((ιStupidTrunc K (embeddingUpIntGE b)).f n) :=
        isIso_ιStupidTrunc_f K _ (i := (n - b).toNat) (by
          show b + (((n - b).toNat : ℕ) : ℤ) = n
          omega)
      have hc : (stupidTruncGEMapLE K h).f n ≫ (ιStupidTrunc K (embeddingUpIntGE a)).f n =
          (ιStupidTrunc K (embeddingUpIntGE b)).f n := by
        rw [← HomologicalComplex.comp_f, stupidTruncGEMapLE_ι]
      rw [(IsIso.eq_comp_inv _).2 hc]
      infer_instance
    · have h₁ : IsZero ((K.stupidTrunc (embeddingUpIntGE b)).X n) :=
        isZero_stupidTrunc_X K _ n ((notMem_range_embeddingUpIntGE_iff _ n).2 (by omega))
      have h₂ : IsZero ((K.stupidTrunc (embeddingUpIntGE a)).X n) := by
        by_cases hna : a ≤ n
        · exact IsZero.of_iso (hz n hna (by omega))
            (stupidTruncXIso K (embeddingUpIntGE a) (i := (n - a).toNat) (by
              show a + (((n - a).toNat : ℕ) : ℤ) = n
              omega))
        · exact isZero_stupidTrunc_X K _ n
            ((notMem_range_embeddingUpIntGE_iff _ n).2 (by omega))
      rw [h₁.eq_of_src ((stupidTruncGEMapLE K h).f n) (h₁.iso h₂).hom]
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end StacksDraft.StupidTruncation

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion of a brutal truncation is an isomorphism in every degree at least `k`. -/
lemma isIso_ιBrutal_f (L : CochainComplex C ℕ) (k n : ℕ) (h : k ≤ n) :
    IsIso ((ιBrutal L k).f n) :=
  (Subobject.isIso_arrow_iff_eq_top (brutalStep L k n)).mpr (by simp [brutalStep, h])

/-- The extension by zero of a brutal truncation vanishes below `k`. -/
instance isStrictlyGE_brutal_extend (L : CochainComplex C ℕ) (k : ℕ) :
    CochainComplex.IsStrictlyGE ((brutal L k).extend embeddingUpNat) (k : ℤ) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases h : ∃ m : ℕ, (m : ℤ) = i
  · obtain ⟨m, rfl⟩ := h
    exact IsZero.of_iso (isZero_brutal_X (k := k) (n := m) L (by omega))
      (HomologicalComplex.extendXIso (brutal L k) embeddingUpNat (i := m) (i' := (m : ℤ)) rfl)
  · exact HomologicalComplex.isZero_extend_X _ _ i (fun m hm => h ⟨m, hm⟩)

/-- The comparison from the extension by zero of the brutal truncation `σ^{≥k}L^•` of an
`ℕ`-indexed complex to Mathlib's stupid truncation `σ^{≥k}` of the extension by zero of `L^•`:
the extension of the inclusion `σ^{≥k}L^• ⟶ L^•` vanishes below `k`, so it factors through the
stupid truncation. -/
def brutalExtendHom (L : CochainComplex C ℕ) (k : ℕ) :
    (brutal L k).extend embeddingUpNat ⟶
      (L.extend embeddingUpNat).stupidTrunc (embeddingUpIntGE (k : ℤ)) :=
  liftStupidTrunc (L.extend embeddingUpNat) (embeddingUpIntGE (k : ℤ))
    (HomologicalComplex.extendMap (ιBrutal L k) embeddingUpNat)

/-- The comparison lies over the inclusions into the extension of `L^•`. -/
@[reassoc (attr := simp)]
lemma brutalExtendHom_ι (L : CochainComplex C ℕ) (k : ℕ) :
    brutalExtendHom L k ≫
        (L.extend embeddingUpNat).ιStupidTrunc (embeddingUpIntGE (k : ℤ)) =
      HomologicalComplex.extendMap (ιBrutal L k) embeddingUpNat :=
  liftStupidTrunc_ι _ _ _

/-- The comparison `CochainComplex.brutalExtendHom` from the extension by zero of `σ^{≥k}L^•` to
the stupid truncation of the extension of `L^•` is an isomorphism. -/
instance isIso_brutalExtendHom (L : CochainComplex C ℕ) (k : ℕ) :
    IsIso (brutalExtendHom L k) := by
  have hcomp : ∀ n : ℤ, IsIso ((brutalExtendHom L k).f n) := by
    intro n
    by_cases hn : (k : ℤ) ≤ n
    · have hnat : embeddingUpNat.f n.toNat = n := by
        change ((n.toNat : ℕ) : ℤ) = n
        omega
      have hge : (embeddingUpIntGE (k : ℤ)).f (n - k).toNat = n := by
        change (k : ℤ) + (((n - k).toNat : ℕ) : ℤ) = n
        omega
      have : IsIso ((ιBrutal L k).f n.toNat) := isIso_ιBrutal_f L k n.toNat (by omega)
      have : IsIso ((HomologicalComplex.extendMap (ιBrutal L k) embeddingUpNat).f n) := by
        rw [HomologicalComplex.extendMap_f _ _ hnat]
        infer_instance
      have : IsIso (((L.extend embeddingUpNat).ιStupidTrunc
          (embeddingUpIntGE (k : ℤ))).f n) :=
        HomologicalComplex.isIso_ιStupidTrunc_f _ _ hge
      have hc : (brutalExtendHom L k).f n ≫
          ((L.extend embeddingUpNat).ιStupidTrunc (embeddingUpIntGE (k : ℤ))).f n =
          (HomologicalComplex.extendMap (ιBrutal L k) embeddingUpNat).f n := by
        rw [← HomologicalComplex.comp_f, brutalExtendHom_ι]
      rw [(IsIso.eq_comp_inv _).2 hc]
      infer_instance
    · have h₁ : IsZero (((brutal L k).extend embeddingUpNat).X n) :=
        CochainComplex.isZero_of_isStrictlyGE _ (k : ℤ) n (by omega)
      have h₂ : IsZero ((((L.extend embeddingUpNat).stupidTrunc
          (embeddingUpIntGE (k : ℤ)))).X n) :=
        HomologicalComplex.isZero_stupidTrunc_X _ _ n
          ((notMem_range_embeddingUpIntGE_iff _ n).2 (by omega))
      rw [h₁.eq_of_src ((brutalExtendHom L k).f n) (h₁.iso h₂).hom]
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The two presentations of the brutal truncation agree.** The extension by zero of the
subobject-cut truncation `σ^{≥k}L^•` of an `ℕ`-indexed cochain complex is Mathlib's stupid
truncation, along `ComplexShape.embeddingUpIntGE k`, of the extension by zero of `L^•`. -/
def brutalExtendIso (L : CochainComplex C ℕ) (k : ℕ) :
    (brutal L k).extend embeddingUpNat ≅
      (L.extend embeddingUpNat).stupidTrunc (embeddingUpIntGE (k : ℤ)) :=
  asIso (brutalExtendHom L k)

end CochainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {E : Type*} [Category* E] [Abelian E]
  (F : C ⥤ E) [F.Additive]

/-- An additive functor sends a degree of a brutal truncation below `k` to a zero object. -/
lemma isZero_map_brutal_X (L : CochainComplex C ℕ) (k n : ℕ) (hn : n < k) :
    IsZero (F.obj ((brutal L k).X n)) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id,
    (isZero_brutal_X (k := k) (n := n) L (by omega)).eq_of_src (𝟙 _) 0, F.map_zero]

/-- The comparison from the image of a brutal truncation under an additive functor to the brutal
truncation of the image: the image of the inclusion `σ^{≥k}L^• ⟶ L^•` vanishes below `k`, so it
factors through `σ^{≥k}F(L)^•`. -/
def mapBrutalHom (L : CochainComplex C ℕ) (k : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (brutal L k) ⟶
      brutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k :=
  liftBrutal _ k ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (ιBrutal L k))
    fun n hn => (isZero_map_brutal_X F L k n hn).eq_of_src _ _

/-- The comparison lies over the inclusions into the image of `L^•`. -/
@[reassoc (attr := simp)]
lemma mapBrutalHom_ι (L : CochainComplex C ℕ) (k : ℕ) :
    mapBrutalHom F L k ≫ ιBrutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (ιBrutal L k) :=
  liftBrutal_ι _ _ _ _

/-- The comparison `CochainComplex.mapBrutalHom` from `F(σ^{≥k}L^•)` to `σ^{≥k}F(L)^•` is an
isomorphism. -/
instance isIso_mapBrutalHom (L : CochainComplex C ℕ) (k : ℕ) :
    IsIso (mapBrutalHom F L k) := by
  have hcomp : ∀ n : ℕ, IsIso ((mapBrutalHom F L k).f n) := by
    intro n
    by_cases hn : k ≤ n
    · have : IsIso ((ιBrutal L k).f n) := isIso_ιBrutal_f L k n hn
      have : IsIso ((ιBrutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k).f n) :=
        isIso_ιBrutal_f _ k n hn
      have : IsIso (((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (ιBrutal L k)).f n) :=
        inferInstanceAs (IsIso (F.map ((ιBrutal L k).f n)))
      have hc : (mapBrutalHom F L k).f n ≫
          (ιBrutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k).f n =
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (ιBrutal L k)).f n := by
        rw [← HomologicalComplex.comp_f, mapBrutalHom_ι]
      rw [(IsIso.eq_comp_inv _).2 hc]
      infer_instance
    · have h₁ : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (brutal L k)).X n) := isZero_map_brutal_X F L k n (by omega)
      have h₂ : IsZero ((brutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k).X n) :=
        isZero_brutal_X (k := k) (n := n) _ (by omega)
      rw [h₁.eq_of_src ((mapBrutalHom F L k).f n) (h₁.iso h₂).hom]
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **An additive functor commutes with the brutal truncation**: `F(σ^{≥k}L^•) ≅ σ^{≥k}F(L)^•`,
both sides being `F` of the terms of `L^•` in degrees `≥ k` and zero below. -/
def mapBrutalIso (L : CochainComplex C ℕ) (k : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (brutal L k) ≅
      brutal ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k :=
  asIso (mapBrutalHom F L k)

/-- The comparison from the image under an additive functor of a brutal truncation, extended by
zero, to the stupid truncation of the extension: the two comparisons of
`CochainComplex.mapBrutalHom` and `CochainComplex.brutalExtendHom` in succession. -/
def mapBrutalExtendHom (L : CochainComplex C ℕ) (k : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (brutal L k)).extend embeddingUpNat ⟶
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extend embeddingUpNat).stupidTrunc
        (embeddingUpIntGE (k : ℤ)) :=
  HomologicalComplex.extendMap (mapBrutalHom F L k) embeddingUpNat ≫
    brutalExtendHom ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) k

/-- **The comparison lies over the inclusions into `F(L)^•`**: composing it with the inclusion of
the stupid truncation returns the extension by zero of the image of the inclusion
`σ^{≥k}L^• ⟶ L^•`. This is what makes `CochainComplex.mapBrutalExtendIso` an identification of
two presentations of one step of the filtration, and not merely of two complexes. -/
@[reassoc (attr := simp)]
lemma mapBrutalExtendHom_ι (L : CochainComplex C ℕ) (k : ℕ) :
    mapBrutalExtendHom F L k ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extend
          embeddingUpNat).ιStupidTrunc (embeddingUpIntGE (k : ℤ)) =
      HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ιBrutal L k)) embeddingUpNat := by
  rw [mapBrutalExtendHom, Category.assoc, brutalExtendHom_ι,
    ← HomologicalComplex.extendMap_comp, mapBrutalHom_ι]

/-- The comparison `CochainComplex.mapBrutalExtendHom` from the extension by zero of
`F(σ^{≥k}L^•)` to the stupid truncation of the extension of `F(L)^•` is an isomorphism. -/
instance isIso_mapBrutalExtendHom (L : CochainComplex C ℕ) (k : ℕ) :
    IsIso (mapBrutalExtendHom F L k) := by
  rw [mapBrutalExtendHom]
  infer_instance

/-- **The two presentations of the `k`-th step of the brutal filtration agree after applying an
additive functor.** The image of the subobject-cut truncation `σ^{≥k}L^•` under `F`, extended by
zero to negative degrees, is Mathlib's stupid truncation along `ComplexShape.embeddingUpIntGE k`
of the extension by zero of `F(L)^•`. -/
def mapBrutalExtendIso (L : CochainComplex C ℕ) (k : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (brutal L k)).extend embeddingUpNat ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extend embeddingUpNat).stupidTrunc
        (embeddingUpIntGE (k : ℤ)) :=
  asIso (mapBrutalExtendHom F L k)

end CochainComplex

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

-- `abelianModules`, `hasSheafifyOpens` and `wEqualsLocallyBijectiveOpens` are `local instance`s
-- of `WedgeFiltration`, and `local` scopes the attribute rather than the name, so the three are
-- re-enabled here instead of being declared again. The last two are what let
-- `SheafOfModules.instAbelian` be found at `Stacks.SheafOfModules.Tensor.ringSheaf A`.
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- The abelianisation functor on `ℕ`-indexed complexes of sheaves of modules: forgetting the
module structure on every term. It is what `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex`
applies to the de Rham complex.

**This abbreviation is an elaboration boundary** and not merely a name for its body. The two
spellings of the base ring sheaf — the `Stacks.SheafOfModules.Tensor.ringSheaf A` that
`deRhamComplex` and the brutal truncations of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Multiplicativity` are stated at, and the
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A` that
`AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex` is stated at — are definitionally equal
only at default transparency, and the two sides of every statement below need one of them each:
the arguments of this functor are truncations, while its values have to be the complexes of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic`. So the domain is declared at the
first spelling and the body is written at the second, and the single unification between them is
discharged here, once, where it is cheap. Inlining the body would reinstate that unification at
every use site, under the reducible transparency a `rw` motive is formed at, where it fails. -/
abbrev abelianisationFunctor :
    CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ ⥤
      CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf X.carrier) ℕ :=
  (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).mapHomologicalComplex
    (ComplexShape.up ℕ)

/-- **The brutal truncation `σ^{≥k}Ω^•_{𝒪_X/A}` that carries the multiplication of the Hodge
filtration is the one the Hodge filtration on hypercohomology is taken of.** Read in abelian
sheaves and extended by zero to negative degrees, the subobject-cut truncation
`AlgebraicGeometry.SheafOfModules.deRhamBrutal` of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Multiplicativity` is the stupid truncation
of `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt` that underlies
`AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlus`.

The two presentations are related in two steps: abelianisation commutes with the brutal truncation
(`CochainComplex.mapBrutalIso`), and the extension by zero of a brutal truncation is the stupid
truncation of the extension (`CochainComplex.brutalExtendIso`). -/
def deRhamBrutalAbelianIso (k : ℕ) :
    ((abelianisationFunctor (A := A)).obj (deRhamBrutal B D k)).extend embeddingUpNat ≅
      (deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE (k : ℤ)) :=
  CochainComplex.mapBrutalExtendIso
    (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)) (deRhamComplex B D) k

/-- **The identification of the two presentations lies over the inclusions into the de Rham
complex of abelian sheaves**: composing it with the inclusion of the stupid truncation returns
the abelianised, extended inclusion of the brutal truncation. -/
theorem deRhamBrutalAbelianIso_hom_ι (k : ℕ) :
    (deRhamBrutalAbelianIso B D k).hom ≫
        (deRhamAbelianComplexInt B D).ιStupidTrunc (embeddingUpIntGE (k : ℤ)) =
      HomologicalComplex.extendMap ((abelianisationFunctor (A := A)).map
        (CochainComplex.ιBrutal (deRhamComplex B D) k)) embeddingUpNat :=
  CochainComplex.mapBrutalExtendHom_ι _ _ k

/-- **The multiplication of the Hodge filtration, read in the presentation that the Hodge
filtration on hypercohomology uses.** The multiplication
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge` of Section 0FM7 is a morphism of complexes
of sheaves of modules into `AlgebraicGeometry.SheafOfModules.deRhamBrutal`; this is it read in
abelian sheaves and extended by zero, so that its target is the stupid truncation of
`AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt` underlying
`AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlus`. -/
def hodgeFiltrationWedgeAbelian (i j : ℕ) :
    ((abelianisationFunctor (A := A)).obj (truncatedTensorSquare B D i j)).extend
        embeddingUpNat ⟶
      (deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE ((i + j : ℕ) : ℤ)) :=
  HomologicalComplex.extendMap
      ((abelianisationFunctor (A := A)).map (hodgeFiltrationWedge B D i j)) embeddingUpNat ≫
    (deRhamBrutalAbelianIso B D (i + j)).hom

/-- **The multiplication of the Hodge filtration is still the wedge product after passing to
abelian sheaves**: composing it with the inclusion `σ^{≥(i + j)}Ω^• ⟶ Ω^•` of complexes of abelian
sheaves returns the abelianised, extended wedge product
`AlgebraicGeometry.SheafOfModules.truncatedWedge`. This is
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge_ιBrutal` in the realization in which the
Hodge-filtered first Chern class of Tag 0FME lives. -/
theorem hodgeFiltrationWedgeAbelian_ι (i j : ℕ) :
    hodgeFiltrationWedgeAbelian B D i j ≫
        (deRhamAbelianComplexInt B D).ιStupidTrunc (embeddingUpIntGE ((i + j : ℕ) : ℤ)) =
      HomologicalComplex.extendMap ((abelianisationFunctor (A := A)).map
        (truncatedWedge B D i j)) embeddingUpNat := by
  rw [hodgeFiltrationWedgeAbelian, Category.assoc, deRhamBrutalAbelianIso_hom_ι,
    ← HomologicalComplex.extendMap_comp, ← Functor.map_comp, hodgeFiltrationWedge_ιBrutal]

end AlgebraicGeometry.SheafOfModules

end
