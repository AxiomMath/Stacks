module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleSections

/-!
# `A`-linear global sections of an internal Hom complex, and the Čech differential in the
inclusion basis

Let `(𝒞, 𝒪)` be a ringed site, let `A` be a commutative ring and let `ρ : A ⟶ Γ(𝒞, 𝒪)` make `𝒪`
a sheaf of `A`-algebras.

The `A`-linear global sections `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver`, that is
`Hom_𝒪(𝒪, -)` with `A` acting through `ρ`, are identified with the compatible families of global
sections with scalars restricted along `ρ`. Through this identification, the description of the
global sections of the internal Hom complex `AlgebraicGeometry.RingedSite.sheafHomComplex` as the
Hom complex of `Comp^dg(𝒪)` ([Stacks, Tag 0A8Z]) holds over `A`.

The differential of `CategoryTheory.AlternatingCech.complex` is described out of the factors of
the source: out of the factor indexed by `S` it is the signed sum, over `i ∉ S`, of the transition
`S ⊆ S ∪ {i}` followed by the inclusion of the factor indexed by `S ∪ {i}`.

## Main definitions

* `CategoryTheory.AlternatingCech.termι`: the inclusion of the factor indexed by a subset `S`
  into the degree-`p` term, the indexing type being finite so that the term is a biproduct.
* `CategoryTheory.AlternatingCech.termDesc`: a morphism out of the degree-`p` term, assembled
  from a family of morphisms out of its factors.
* `CategoryTheory.AlternatingCech.insertIdx`: the index `S ∪ {i}` of cardinality `p + 1`.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverSectionsEquiv` and
  `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIso`: the identification of `A`-linear
  global sections with compatible global sections, as an `A`-linear equivalence and as a natural
  isomorphism of functors.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverComplexIso`: the same identification on
  complexes.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso`: [Stacks, Tag 0A8Z] over
  `A`.

## Main results

* `CategoryTheory.AlternatingCech.termι_comp_termDesc`,
  `CategoryTheory.AlternatingCech.termDesc_comp_termι` and
  `CategoryTheory.AlternatingCech.term_hom_ext`: morphisms out of the degree-`p` term are exactly
  the finite families of morphisms out of its factors.
* `CategoryTheory.AlternatingCech.termι_comp_d`: out of the factor indexed by `S` the alternating
  Čech differential is
  `∑_{i ∉ S} (-1)^{#\{j ∈ S : j < i\}} · (transition S ⊆ S ∪ \{i\}) ≫ (inclusion of S ∪ \{i\})`.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverHomComplexIso_hom_f_apply`: the
  identification over `A` sends a morphism to the cochain determined by the global section it
  names.

## Implementation notes

`CategoryTheory.AlternatingCech.termι_comp_d` is the form of the differential used by
`AlgebraicGeometry.RingedSite.globalSectionsKoszulSheafHomComplexSystemIso` of
`KoszulGlobalHomCochain.lean`, which identifies, for `f_i = ρ(a_i)` and
`K^n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`, the tower `n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))` with
`KoszulCoefficientTower.coefficientKoszulTower a` applied to `Γ_A(𝒞, J)`. Both towers are
graded by the degrees `0, …, r` of the Koszul complex:
`KoszulCoefficientTower.coefficientKoszulTerm K t = ∀ S : Finset (Fin r), K.X (t + #S)` is
`Hom•_A(Kos(a^{n+1}), K)`, since `Hom(∏_{#S = p} A, K^{t+p}) = ∏_{#S = p} K^{t+p}`.

The two differentials differ by a sign. Mathlib's `δ` has
`(δ t (t+1) z).v p q = z.v p (p+t) ≫ G.d (p+t) q + (-1)^{t+1} • F.d p (p+1) ≫ z.v (p+1) q`, so by
`termι_comp_d` the contraction term of `Γ(𝒞, SheafHom•_𝒪(K^n, J))` at the factor `S` carries the
sign `(-1)^{t+1} · (-1)^{#\{j ∈ S : j < i\}}`, whereas
`KoszulCoefficientTower.coefficientKoszulDifferential` carries
`(-1)^{t + #S + 1} · (-1)^{#\{j ∈ S : j < i\}}`. The two differ by `(-1)^{#S}` on that term and
agree on the coefficient term, so the degreewise identification is twisted by the sign
`ε_S = (-1)^{#S(#S - 1)/2}`, which satisfies `ε_{S ∪ \{i\}} = (-1)^{#S} ε_S`. The transition maps
need no twist: on both sides they multiply the factor `S` by `∏_{i ∈ S} a_i^{m - n}`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u

/-! ## Morphisms out of an alternating Čech term -/

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasFiniteBiproducts 𝒜]
  (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ}

/-- The inclusion of the factor indexed by `S` into the degree-`p` term, the product over the
finite type `CategoryTheory.AlternatingCech.Idx r p` of subsets of cardinality `p` being a finite
biproduct. -/
def termι (S : Idx r p) : F.obj S.1 ⟶ term F p :=
  biproduct.ι (fun T : Idx r p ↦ F.obj T.1) S ≫ (biproduct.isoProduct _).hom

/-- The inclusion of the factor indexed by `S` followed by the projection onto it is the
identity. -/
@[simp, reassoc]
theorem termι_comp_π_self (S : Idx r p) :
    termι F S ≫ Pi.π (fun T : Idx r p ↦ F.obj T.1) S = 𝟙 _ := by
  rw [termι, Category.assoc, biproduct.isoProduct_hom, Pi.lift_π, biproduct.ι_π_self]

/-- The inclusion of the factor indexed by `S` followed by the projection onto a different
factor `T` is zero. -/
@[reassoc]
theorem termι_comp_π_of_ne {S T : Idx r p} (h : S ≠ T) :
    termι F S ≫ Pi.π (fun W : Idx r p ↦ F.obj W.1) T = 0 := by
  rw [termι, Category.assoc, biproduct.isoProduct_hom, Pi.lift_π,
    biproduct.ι_π_ne _ h]

/-- The sum over all factors of projection followed by inclusion is the identity of the
degree-`p` term. -/
theorem π_comp_termι_sum :
    ∑ S : Idx r p, Pi.π (fun T : Idx r p ↦ F.obj T.1) S ≫ termι F S = 𝟙 (term F p) := by
  refine Pi.hom_ext _ _ fun T ↦ ?_
  rw [Preadditive.sum_comp, Finset.sum_eq_single T]
  · rw [Category.assoc, termι_comp_π_self, Category.comp_id, Category.id_comp]
  · intro S _ hS
    rw [Category.assoc, termι_comp_π_of_ne F hS, comp_zero]
  · exact fun h ↦ absurd (Finset.mem_univ T) h

/-- The morphism out of the degree-`p` term whose restriction to the factor indexed by `S` is
`g S`. -/
def termDesc {Z : 𝒜} (g : ∀ S : Idx r p, F.obj S.1 ⟶ Z) : term F p ⟶ Z :=
  ∑ S : Idx r p, Pi.π (fun T : Idx r p ↦ F.obj T.1) S ≫ g S

/-- The restriction of `termDesc F g` to the factor indexed by `S` is `g S`. -/
@[simp, reassoc]
theorem termι_comp_termDesc {Z : 𝒜} (g : ∀ S : Idx r p, F.obj S.1 ⟶ Z) (S : Idx r p) :
    termι F S ≫ termDesc F g = g S := by
  rw [termDesc, Preadditive.comp_sum, Finset.sum_eq_single S]
  · rw [termι_comp_π_self_assoc]
  · intro T _ hT
    rw [termι_comp_π_of_ne_assoc F (Ne.symm hT), zero_comp]
  · exact fun h ↦ absurd (Finset.mem_univ S) h

/-- A morphism out of the degree-`p` term is assembled from its restrictions to the factors. -/
@[simp]
theorem termDesc_comp_termι {Z : 𝒜} (h : term F p ⟶ Z) :
    termDesc F (fun S ↦ termι F S ≫ h) = h := by
  rw [termDesc]
  simp only [← Category.assoc]
  rw [← Preadditive.sum_comp, π_comp_termι_sum, Category.id_comp]

/-- Two morphisms out of the degree-`p` term agreeing on every factor are equal. -/
theorem term_hom_ext {Z : 𝒜} {h h' : term F p ⟶ Z}
    (hyp : ∀ S : Idx r p, termι F S ≫ h = termι F S ≫ h') : h = h' := by
  rw [← termDesc_comp_termι F h, ← termDesc_comp_termι F h']
  exact congrArg (termDesc F) (funext hyp)

/-- The index `S ∪ {i}` of cardinality `p + 1`, for `i` outside `S`. -/
abbrev insertIdx (S : Idx r p) (i : {x : Fin r // x ∉ S.1}) : Idx r (p + 1) :=
  ⟨insert i.1 S.1, by
    rw [Finset.card_insert_of_notMem i.2, Nat.cast_add, Nat.cast_one, S.2]⟩

/-- `S` is contained in `S ∪ {i}`. -/
theorem subset_insertIdx (S : Idx r p) (i : {x : Fin r // x ∉ S.1}) :
    S.1 ⊆ (insertIdx S i).1 :=
  Finset.subset_insert i.1 S.1

/-- Inserting two distinct indices outside `S` gives two distinct subsets. -/
theorem insertIdx_injective (S : Idx r p) {i j : {x : Fin r // x ∉ S.1}}
    (h : insertIdx S i = insertIdx S j) : i = j := by
  have hv : insert i.1 S.1 = insert j.1 S.1 := congrArg Subtype.val h
  have hi : i.1 ∈ insert j.1 S.1 := hv ▸ Finset.mem_insert_self i.1 S.1
  exact Subtype.ext ((Finset.mem_insert.1 hi).resolve_right i.2)

variable {F}

/-- Out of the factor indexed by `S`, the alternating Čech differential is the signed sum, over
the indices `i` outside `S`, of the transition map `F.obj S ⟶ F.obj (S ∪ {i})` followed by the
inclusion of the factor indexed by `S ∪ {i}`. -/
theorem termι_comp_d (S : Idx r p) :
    termι F S ≫ d F p =
      ∑ i : {i : Fin r // i ∉ S.1}, Cech.cechSign (insertIdx S i).1 i.1 •
        (F.map (homOfLE (subset_insertIdx S i)) ≫ termι F (insertIdx S i)) := by
  refine Pi.hom_ext _ _ fun T ↦ ?_
  rw [Category.assoc, d_comp_pi, Preadditive.comp_sum, Preadditive.sum_comp]
  have hleft : ∀ k : {x // x ∈ T.1}, T.erase k ≠ S →
      termι F S ≫ (Cech.cechSign T.1 k.1 • proj F (T.erase k) (T.erase_subset k)) = 0 := by
    intro k hk
    rw [Preadditive.comp_zsmul, proj, ← Category.assoc,
      termι_comp_π_of_ne F (Ne.symm hk), zero_comp, smul_zero]
  have hright : ∀ i : {i : Fin r // i ∉ S.1}, insertIdx S i ≠ T →
      (Cech.cechSign (insertIdx S i).1 i.1 •
        (F.map (homOfLE (subset_insertIdx S i)) ≫ termι F (insertIdx S i))) ≫
          Pi.π (fun W : Idx r (p + 1) ↦ F.obj W.1) T = 0 := by
    intro i hi
    rw [Preadditive.zsmul_comp, Category.assoc, termι_comp_π_of_ne F hi, comp_zero, smul_zero]
  have herase_val : ∀ k : {x // x ∈ T.1}, T.erase k = S → T.1.erase k.1 = S.1 := fun k hS ↦ by
    simpa using congrArg Subtype.val hS
  by_cases hT : ∃ i : {i : Fin r // i ∉ S.1}, insertIdx S i = T
  · obtain ⟨i, rfl⟩ := hT
    have hmem : i.1 ∈ (insertIdx S i).1 := Finset.mem_insert_self i.1 S.1
    have herase : (insertIdx S i).erase ⟨i.1, hmem⟩ = S :=
      Subtype.ext (by simpa using Finset.erase_insert i.2)
    rw [Finset.sum_eq_single (⟨i.1, hmem⟩ : {x // x ∈ (insertIdx S i).1}), Finset.sum_eq_single i]
    · rw [Preadditive.zsmul_comp, Category.assoc, termι_comp_π_self, Category.comp_id,
        Preadditive.comp_zsmul]
      refine congrArg (fun x ↦ Cech.cechSign (insertIdx S i).1 i.1 • x) ?_
      rw [proj_congr F herase (h' := subset_insertIdx S i), proj, ← Category.assoc,
        termι_comp_π_self, Category.id_comp]
    · exact fun j _ hj ↦ hright j fun h ↦ hj (insertIdx_injective S h)
    · exact fun h ↦ absurd (Finset.mem_univ i) h
    · refine fun k _ hk ↦ hleft k fun hS ↦ hk (Subtype.ext ?_)
      by_contra hki
      have hmem' : i.1 ∈ (insertIdx S i).1.erase k.1 :=
        Finset.mem_erase.2 ⟨fun h ↦ hki h.symm, Finset.mem_insert_self i.1 S.1⟩
      rw [herase_val k hS] at hmem'
      exact i.2 hmem'
    · exact fun h ↦ absurd (Finset.mem_attach _ _) h
  · refine Eq.trans (Finset.sum_eq_zero fun k _ ↦ hleft k ?_)
      (Finset.sum_eq_zero fun i _ ↦ hright i ?_).symm
    · intro hS
      have hv := herase_val k hS
      exact hT ⟨⟨k.1, hv ▸ Finset.notMem_erase k.1 T.1⟩,
        Subtype.ext (by simpa [hv] using Finset.insert_erase k.2)⟩
    · exact fun h ↦ hT ⟨i, h⟩

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-! ## `Hom_𝒪(𝒪, ℱ)` is the module of global sections, `A`-linearly -/

/-- The `A`-linear equivalence between `Hom_𝒪(𝒪, M)`, with `A` acting through `ρ`, and the
compatible global sections of `M` with scalars restricted along `ρ`, given by
`SheafOfModules.unitHomEquiv`. -/
def moduleGlobalSectionsOverSectionsEquiv
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (moduleGlobalSectionsOver X A ρ).obj M ≃ₗ[A]
      ((ModuleCat.restrictScalars ρ).obj ((globalSectionsModules X).obj M)) where
  toFun f := M.unitHomEquiv f
  invFun s := M.unitHomEquiv.symm s
  left_inv f := M.unitHomEquiv.symm_apply_apply f
  right_inv s := M.unitHomEquiv.apply_symm_apply s
  map_add' _ _ := rfl
  map_smul' a f := Subtype.ext <| funext fun U ↦
    (f.val.app U).hom.map_smul ((ρ a).1 U)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)

/-- The natural isomorphism between `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver`,
which is `Hom_𝒪(𝒪, -)` over `A`, and `AlgebraicGeometry.RingedSite.globalSectionsModules`
([Stacks, Tag 071H]) followed by restriction of scalars along `ρ`. -/
def moduleGlobalSectionsOverIso :
    moduleGlobalSectionsOver X A ρ ≅
      globalSectionsModules X ⋙ ModuleCat.restrictScalars ρ :=
  NatIso.ofComponents
    (fun M ↦ (moduleGlobalSectionsOverSectionsEquiv X A ρ M).toModuleIso)
    (fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

/-- The isomorphism `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIso` applied
degreewise to a complex. -/
def moduleGlobalSectionsOverComplexIso
    (K : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (globalSectionsModulesComplex X K) :=
  ((NatIso.mapHomologicalComplex (moduleGlobalSectionsOverIso X A ρ)
      (ComplexShape.up ℤ)).app K).trans
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (globalSectionsModules X ⋙ ModuleCat.restrictScalars ρ))
      (ComplexShape.up ℤ)).app K).symm

/-! ## [Stacks, Tag 0A8Z] over `A` -/

variable {X}

/-- The complex of `A`-linear global sections of the internal Hom complex of `F` and `G` is the
Hom complex of the differential graded category `Comp^dg(𝒪)`, with scalars restricted along `ρ`
([Stacks, Tag 0A8Z]). -/
def moduleGlobalSectionsOverHomComplexIso
    (F G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sheafHomComplex X F G).obj ≅
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          F G) :=
  (moduleGlobalSectionsOverComplexIso X A ρ (sheafHomComplex X F G).obj).trans
    (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (globalSectionsHomComplexModulesIso F G))

/-- `moduleGlobalSectionsOverHomComplexIso` sends a morphism `𝒪 ⟶ SheafHom•(F, G)^n` to the
cochain determined by the global section it names. -/
theorem moduleGlobalSectionsOverHomComplexIso_hom_f_apply
    (F G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)
    (n : ℤ)
    (f : ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (sheafHomComplex X F G).obj |>.X n) :
    (moduleGlobalSectionsOverHomComplexIso A ρ F G).hom.f n f =
      (show Cochain F G n from
        ((sheafHomComplex X F G).globalSectionsIso.hom.f n
          (((sheafHomComplex X F G).obj.X n).unitHomEquiv f)).down) :=
  rfl

end AlgebraicGeometry.RingedSite

end
