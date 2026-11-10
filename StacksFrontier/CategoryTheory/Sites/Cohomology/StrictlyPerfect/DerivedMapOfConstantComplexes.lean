module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfAConstantComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteModelComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteTwoReadings
public import StacksFrontier.Homology.Perfect.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Maps between constant complexes are locally constant in the derived category

Let `(C, J)` be a small site, `Λ` a commutative ring, and write `K ↦ K̲` for the functor
`D(Λ) ⥤ D(C, Λ)` induced by the constant sheaf functor. Stacks 09BE says: if `K` is perfect,
then every morphism `φ : K̲ ⟶ L̲` of `D(C, Λ)` is, on the members `U_i` of a covering of the
final object, equal to `α̲_i` for some morphism `α_i : K ⟶ L` of `D(Λ)`.

## Main results

* `Stacks.ConstantDerivedMap.exists_cover_overPullback_map_eq_overConstantSheaf_map`:
  **Stacks 09BE**, over an arbitrary object `X` of the site, with `α̲_i` the constant map on the
  slice site `C/U_i`.
* `Stacks.ConstantDerivedMap.exists_cover_overPullback_map_eq_constantSheaf_map`: the same, with
  `α̲_i` read as the restriction of the constant map on `C`.
* `Stacks.ConstantDerivedMap.overConstantSheafMapDerivedCategoryIso`: on derived categories, the
  constant complex on `C/U` is the restriction of the constant complex on `C`.
* `Stacks.ConstantDerivedMap.exists_cover_Q_map_overMapPullback_eq`: a roof
  `P̲|_X ⟶ W ⟵ F` in `Sheaf (J.over X) (ModuleCat Λ)` out of the restriction of a bounded
  complex of finite projective `Λ`-modules factors, on a covering sieve of `X`, in the derived
  category. This is Stacks 09BD transported to `ModuleCat Λ`-valued sheaves.

## Implementation notes

The source's proof is "Lemma 09BD and Modules on Sites, Lemma 093S", and this is how it goes
here:

1. `φ` is written as a roof `Q(b) ≫ Q(s)⁻¹` between complexes of sheaves
   (`DerivedCategory.left_fac`) after replacing `K` by a bounded complex `P` of finite
   projective modules and `L` by a complex `T`.
2. Stacks 09BD, `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_constant_general`, is
   stated for sheaves of modules over the restricted structure sheaf of the constant ringed
   site. The roof is carried there along the equivalence
   `Stacks.ConstantRingModules.toModuleSheaf` (an equivalence, by
   `Stacks.ConstantRingModules.toModuleSheaf_isEquivalence`), and the chain map 09BD produces is
   carried back using `Stacks.ConstantRingModules.toModuleSheafOverMapIso`, its compatibility with
   restriction along an arrow of the site. The bookkeeping of this crossing is done abstractly in
   `Stacks.ConstantDerivedMap.exists_Q_map_eq_comp_of_equivalence`.
3. The resulting chain map between restrictions of the complexes of constant sheaves `P̲` and
   `T̲` is locally constant by
   `Stacks.ConstantSheaf.exists_cover_overPullback_eq_constantSheaf_mapHomologicalComplex`, which
   is the appeal to Stacks 093S at the level of complexes. Composing the two coverings
   (`CategoryTheory.GrothendieckTopology.bind_covering`) and reading the factorization through
   the restriction functor on derived categories gives the statement.

The restriction `φ|_{U_i}` is the image of `φ` under the functor on derived categories induced by
`J.overPullback (ModuleCat Λ) U_i`. The registered statement reads `α̲_i` literally, as the map
induced by the constant sheaf functor of `C/U_i`, transported along the canonical isomorphism
`Stacks.ConstantDerivedMap.overConstantSheafMapDerivedCategoryIso` (induced by
`Stacks.ConstantSheaf.overPullbackConstantSheafIso`) between `(K̲)|_{U_i}` and the constant
complex `K̲` on `C/U_i`; it also records the equivalent equation `φ|_{U_i} = (α̲_i)|_{U_i}`.

The site is small and the modules live in its universe, the library's standard one-universe
convention for sheaves of modules on a site;
the three derived categories involved are taken with arbitrary models
(`HasDerivedCategory` instances), so the statement covers in particular
`HasDerivedCategory.standard`. The ring is commutative, as are all rings of the Stacks
Project; the final object of the source is replaced by an arbitrary object `X`, which is a
generalization.

## References

* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe d d' d'' u

namespace Stacks.ConstantDerivedMap

section Generic

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- An exact functor carries maps of complexes with the same image in the derived category to
maps with the same image in the derived category. -/
theorem Q_map_mapHomologicalComplex_eq {K L : CochainComplex A ℤ} {x y : K ⟶ L}
    (h : DerivedCategory.Q.map x = DerivedCategory.Q.map y) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map x) =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map y) := by
  rw [← cancel_epi (H.mapDerivedCategoryFactors.hom.app K),
    ← H.mapDerivedCategoryFactors_hom_naturality, ← H.mapDerivedCategoryFactors_hom_naturality, h]

/-- The composite form of `Q_map_mapHomologicalComplex_eq`. -/
theorem Q_map_mapHomologicalComplex_eq_comp {K L M : CochainComplex A ℤ} {x : K ⟶ M}
    {y : K ⟶ L} {z : L ⟶ M}
    (h : DerivedCategory.Q.map x = DerivedCategory.Q.map (y ≫ z)) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map x) =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map y ≫
        (H.mapHomologicalComplex (ComplexShape.up ℤ)).map z) := by
  rw [← Functor.map_comp]
  exact Q_map_mapHomologicalComplex_eq H h

/-- If an exact functor `H` carries the roof `Q(b) ≫ Q(s)⁻¹` to the class of a chain map `β`,
then `H(b)` and `β ≫ H(s)` have the same class in the derived category. -/
theorem Q_map_eq_comp_of_mapDerivedCategory {E F W : CochainComplex A ℤ} (b : E ⟶ W)
    (s : F ⟶ W) [IsIso (DerivedCategory.Q.map s)]
    (β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (h : H.mapDerivedCategory.map (DerivedCategory.Q.map b ≫ inv (DerivedCategory.Q.map s)) ≫
        H.mapDerivedCategoryFactors.hom.app F =
      H.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map b) =
      DerivedCategory.Q.map (β ≫ (H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have hb : DerivedCategory.Q.map b =
      (DerivedCategory.Q.map b ≫ inv (DerivedCategory.Q.map s)) ≫ DerivedCategory.Q.map s :=
    (IsIso.comp_inv_eq _).1 rfl
  rw [← cancel_epi (H.mapDerivedCategoryFactors.hom.app E),
    ← H.mapDerivedCategoryFactors_hom_naturality, hb, Functor.map_comp, Category.assoc,
    H.mapDerivedCategoryFactors_hom_naturality, ← Category.assoc, h, Category.assoc,
    ← Functor.map_comp]

/-- If `ψ ≫ Q(s) = Q(b)` and an exact functor `H` carries `b` to `H(g) ≫ H(s)` up to the
derived category, then `H` carries `ψ` and `Q(g)` to the same morphism. -/
theorem mapDerivedCategory_map_eq_of_roof {K L W : CochainComplex A ℤ}
    (ψ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) (b : K ⟶ W) (s : L ⟶ W)
    [IsIso (DerivedCategory.Q.map s)]
    (hψ : ψ ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map b) (g : K ⟶ L)
    (hg : DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map b) =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
        (H.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    H.mapDerivedCategory.map ψ = H.mapDerivedCategory.map (DerivedCategory.Q.map g) := by
  rw [← cancel_mono (H.mapDerivedCategory.map (DerivedCategory.Q.map s) ≫
    H.mapDerivedCategoryFactors.hom.app W), ← Category.assoc, ← Functor.map_comp, hψ,
    H.mapDerivedCategoryFactors_hom_naturality, hg, Functor.map_comp, ← Category.assoc,
    ← H.mapDerivedCategoryFactors_hom_naturality]
  simp only [Category.assoc, H.mapDerivedCategoryFactors_hom_naturality]
  rw [reassoc_of% (H.mapDerivedCategoryFactors_hom_naturality g)]

/-- An exact functor carries a quasi-isomorphism, in the form of a map inverted in the derived
category, to one. -/
theorem isIso_Q_map_mapHomologicalComplex {K L : CochainComplex A ℤ} (s : K ⟶ L)
    [IsIso (DerivedCategory.Q.map s)] :
    IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
  have h : DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) =
      (H.mapDerivedCategoryFactors.app K).inv ≫ H.mapDerivedCategory.map (DerivedCategory.Q.map s) ≫
        (H.mapDerivedCategoryFactors.app L).hom :=
    (Iso.eq_inv_comp _).2 (H.mapDerivedCategoryFactors_hom_naturality s).symm
  rw [h]
  infer_instance

end Generic

section Square

variable {𝒜 𝒜' ℬ ℬ' : Type*} [Category* 𝒜] [Category* 𝒜'] [Category* ℬ] [Category* ℬ']
  [Abelian 𝒜] [Abelian 𝒜'] [Abelian ℬ] [Abelian ℬ'] [HasDerivedCategory 𝒜']
  [HasDerivedCategory ℬ']
  (e : 𝒜 ≌ ℬ) [e.functor.Additive] [e.inverse.Additive]
  (H : 𝒜 ⥤ 𝒜') [H.Additive] (T : 𝒜' ⥤ ℬ') [T.Additive] [PreservesFiniteLimits T]
  [PreservesFiniteColimits T] (M : ℬ ⥤ ℬ') [M.Additive]
  (ι : e.functor ⋙ M ≅ H ⋙ T)

include ι

omit [e.inverse.Additive] in
/-- **A local factorization crosses an equivalence compatible with restriction.** Let
`e : 𝒜 ≌ ℬ` be an equivalence of abelian categories, and let `H : 𝒜 ⥤ 𝒜'` and `M : ℬ ⥤ ℬ'`
be restriction functors that `e` and an exact `T : 𝒜' ⥤ ℬ'` intertwine. If a roof `E ⟶ W ⟵ F`
on the `ℬ` side, carried to `𝒜` along `e`, becomes after `H` a factorization in the derived
category, then after `M` the roof itself factors in the derived category. -/
theorem exists_Q_map_eq_comp_of_equivalence {E : CochainComplex 𝒜 ℤ}
    {A F W : CochainComplex ℬ ℤ}
    (ε : (e.mapHomologicalComplex (ComplexShape.up ℤ)).functor.obj E ≅ A) (g : A ⟶ W)
    (s : F ⟶ W)
    (β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((e.mapHomologicalComplex (ComplexShape.up ℤ)).inverse.obj F))
    (h : DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((e.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app E ≫
          (e.mapHomologicalComplex (ComplexShape.up ℤ)).inverse.map (ε.hom ≫ g))) =
      DerivedCategory.Q.map (β ≫ (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((e.mapHomologicalComplex (ComplexShape.up ℤ)).inverse.map s))) :
    ∃ γ : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⟶
        (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
      DerivedCategory.Q.map ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map g) =
        DerivedCategory.Q.map (γ ≫ (M.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let M' := M.mapHomologicalComplex (ComplexShape.up ℤ)
  let T' := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let H' := H.mapHomologicalComplex (ComplexShape.up ℤ)
  let y := ε.hom ≫ g
  let b₂ := eC.unit.app E ≫ eC.inverse.map y
  let s₂ := eC.inverse.map s
  have h2 : DerivedCategory.Q.map (T'.map (H'.map b₂)) =
      DerivedCategory.Q.map (T'.map β ≫ T'.map (H'.map s₂)) :=
    Q_map_mapHomologicalComplex_eq_comp T h
  let ι' : eC.functor ⋙ M' ≅ H' ⋙ T' :=
    Functor.mapHomologicalComplexCompIso ι (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ T)) (ComplexShape.up ℤ)).symm
  have nat2 : ∀ {K L : CochainComplex 𝒜 ℤ} (x : K ⟶ L),
      T'.map (H'.map x) ≫ ι'.inv.app L = ι'.inv.app K ≫ M'.map (eC.functor.map x) :=
    fun x => ι'.inv.naturality x
  have nat1 : ∀ {K L : CochainComplex 𝒜 ℤ} (x : K ⟶ L),
      ι'.hom.app K ≫ T'.map (H'.map x) ≫ ι'.inv.app L = M'.map (eC.functor.map x) := by
    intro K L x
    rw [nat2, Iso.hom_inv_id_app_assoc]
  have hy : eC.functor.map b₂ ≫ eC.counit.app W = y := by
    have n1 : eC.functor.map (eC.inverse.map y) ≫ eC.counit.app W = eC.counit.app _ ≫ y :=
      eC.counit.naturality y
    have n2 : eC.functor.map (eC.unit.app E) ≫ eC.counit.app (eC.functor.obj E) = 𝟙 _ :=
      eC.functor_unit_comp E
    rw [Functor.map_comp, Category.assoc, n1, ← Category.assoc]
    exact (congrArg (· ≫ y) n2).trans (Category.id_comp y)
  have hs : eC.functor.map s₂ ≫ eC.counit.app W = eC.counit.app F ≫ s :=
    eC.counit.naturality s
  refine ⟨M'.map ε.inv ≫ ι'.hom.app E ≫ T'.map β ≫ ι'.inv.app _ ≫ M'.map (eC.counit.app F), ?_⟩
  have e1 : M'.map g = (M'.map ε.inv ≫ ι'.hom.app E) ≫ T'.map (H'.map b₂) ≫
      (ι'.inv.app _ ≫ M'.map (eC.counit.app W)) := by
    rw [Category.assoc, reassoc_of% (nat1 b₂), ← M'.map_comp, ← M'.map_comp, hy]
    simp only [y, Iso.inv_hom_id_assoc]
  have k : T'.map (H'.map s₂) ≫ ι'.inv.app _ ≫ M'.map (eC.counit.app W) =
      ι'.inv.app _ ≫ M'.map (eC.counit.app F) ≫ M'.map s := by
    rw [reassoc_of% (nat2 s₂), ← M'.map_comp, hs, M'.map_comp]
  have e2 : (M'.map ε.inv ≫ ι'.hom.app E ≫ T'.map β ≫ ι'.inv.app _ ≫ M'.map (eC.counit.app F)) ≫
      M'.map s = (M'.map ε.inv ≫ ι'.hom.app E) ≫ (T'.map β ≫ T'.map (H'.map s₂)) ≫
      (ι'.inv.app _ ≫ M'.map (eC.counit.app W)) := by
    simp only [Category.assoc, k]
    rfl
  rw [e1, e2, Functor.map_comp DerivedCategory.Q (M'.map ε.inv ≫ ι'.hom.app E),
    Functor.map_comp DerivedCategory.Q (T'.map (H'.map b₂)),
    Functor.map_comp DerivedCategory.Q (M'.map ε.inv ≫ ι'.hom.app E),
    Functor.map_comp DerivedCategory.Q (T'.map β ≫ T'.map (H'.map s₂)), h2]

end Square

section Transport

open AlgebraicGeometry.RingedSite Stacks.ConstantRingModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]

/-- The constant sheaf functor on `Λ`-modules preserves finite colimits: it is the composite of
the constant presheaf functor and sheafification, both left adjoints. -/
instance preservesFiniteColimits_constantSheaf_moduleCat :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{u} Λ)) := by
  unfold constantSheaf
  infer_instance

section Restriction

variable [∀ V : C, HasDerivedCategory.{d} (Sheaf (J.over V) (ModuleCat.{u} Λ))]

/-- A factorization in `D(C/V)` of the restriction along `f : V ⟶ U` of a map restricted to
`C/U` is a factorization of the restriction of that map to `C/V`. -/
theorem exists_Q_map_overPullback_eq_of_overMapPullback {U V : C} (f : V ⟶ U)
    {K L N : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ} (g : K ⟶ N) (s : L ⟶ N)
    (h : ∃ γ : ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⟶
        ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L),
        DerivedCategory.Q.map (((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g)) =
        DerivedCategory.Q.map (γ ≫ ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map s))) :
    ∃ γ : ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
        ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj L,
      DerivedCategory.Q.map (((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) =
        DerivedCategory.Q.map (γ ≫ ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) :=
  h

/-- If a map restricted to `C/V` factors in `D(C/V)` through a map `δ` whose restriction along
`h : W ⟶ V` is the restriction of a map `c` defined on `C`, then the restriction of the map to
`C/W` factors through the restriction of `c`. -/
theorem Q_map_overPullback_eq_of_overMapPullback {V W : C} (h : W ⟶ V)
    [(J.overMapPullback (ModuleCat.{u} Λ) h).Additive]
    [PreservesFiniteLimits (J.overMapPullback (ModuleCat.{u} Λ) h)]
    [PreservesFiniteColimits (J.overMapPullback (ModuleCat.{u} Λ) h)]
    {K L N : CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ} (g : K ⟶ N) (s : L ⟶ N)
    (δ : ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (hδ : DerivedCategory.Q.map (((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) =
      DerivedCategory.Q.map (δ ≫ ((J.overPullback (ModuleCat.{u} Λ) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s))
    (c : K ⟶ L)
    (hc : ∀ n, (J.overMapPullback (ModuleCat.{u} Λ) h).map (δ.f n) =
      (J.overPullback (ModuleCat.{u} Λ) W).map (c.f n)) :
    DerivedCategory.Q.map (((J.overPullback (ModuleCat.{u} Λ) W).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) =
      DerivedCategory.Q.map (((J.overPullback (ModuleCat.{u} Λ) W).mapHomologicalComplex
        (ComplexShape.up ℤ)).map c ≫ ((J.overPullback (ModuleCat.{u} Λ) W).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) := by
  have h1 := Q_map_mapHomologicalComplex_eq_comp (J.overMapPullback (ModuleCat.{u} Λ) h) hδ
  have hc' : ((J.overMapPullback (ModuleCat.{u} Λ) h).mapHomologicalComplex
      (ComplexShape.up ℤ)).map δ =
      ((J.overPullback (ModuleCat.{u} Λ) W).mapHomologicalComplex (ComplexShape.up ℤ)).map c :=
    HomologicalComplex.hom_ext _ _ hc
  rw [hc'] at h1
  exact h1

end Restriction

/-- **Stacks 09BD in `ModuleCat Λ`-valued sheaves, for a roof.** Let `P` be a bounded complex
of finite projective `Λ`-modules and let `P̲|_X ⟶ W ⟵ F` be a roof of complexes of sheaves of
`Λ`-modules on `C/X` whose second leg is inverted in the derived category. Then on a covering
sieve of `X`, after restriction along each of its arrows `f`, the first leg factors through the
second in the derived category. -/
theorem exists_cover_Q_map_overMapPullback_eq
    [∀ V : C, HasDerivedCategory.{d} (Sheaf (J.over V) (ModuleCat.{u} Λ))]
    {P : CochainComplex (ModuleCat.{u} Λ) ℤ} (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    (X : C) {F W : CochainComplex (Sheaf (J.over X) (ModuleCat.{u} Λ)) ℤ}
    (g : ((J.overPullback (ModuleCat.{u} Λ) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶ W)
    (s : F ⟶ W) [IsIso (DerivedCategory.Q.map s)] :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ {V : C} (f : V ⟶ X), S f →
      ∃ γ : ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((J.overPullback (ModuleCat.{u} Λ) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ⟶
        ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
        DerivedCategory.Q.map
            (((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map g) =
          DerivedCategory.Q.map (γ ≫
            ((J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map s) := by
  classical
  let c := constantSheaf J (ModuleCat.{u} Λ)
  let G := J.overPullback (ModuleCat.{u} Λ) X
  let ρ := constantRingedSiteRingMap J Λ
  let TX := toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J ρ X)
  let e := TX.asEquivalence
  let : e.functor.Additive := inferInstanceAs TX.Additive
  let : e.inverse.Additive := e.inverse_additive
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let Φ := constantFunctorOver_general J Λ X
  let κ : Φ ⋙ TX ≅ c ⋙ G :=
    Functor.isoWhiskerLeft Φ
        (eqToIso (constantRingedSiteModuleEquivalence_functor_eq J Λ X).symm) ≪≫
      constantFunctorOverIso J Λ X ≪≫
      (Stacks.ConstantSheaf.overPullbackConstantSheafIso J (ModuleCat.{u} Λ) X)
  let E := (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let ε : eC.functor.obj E ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (NatIso.mapHomologicalComplex κ (ComplexShape.up ℤ)).app P
  let y := ε.hom ≫ g
  let b₂ := eC.unit.app E ≫ eC.inverse.map y
  let s₂ := eC.inverse.map s
  let : HasDerivedCategory
      (_root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over X)) :=
    HasDerivedCategory.standard _
  have : IsIso (DerivedCategory.Q.map s₂) := isIso_Q_map_mapHomologicalComplex e.inverse s
  obtain ⟨S, hS, hBD⟩ := exists_coveringSieve_complexMap_constant_general J Λ X a b hfin hproj
    (DerivedCategory.Q.map b₂ ≫ inv (DerivedCategory.Q.map s₂))
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, β, hβ⟩ := hBD f hf
  let H := _root_.SheafOfModules.overMap.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O) f
  let : HasDerivedCategory
      (_root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over V)) :=
    HasDerivedCategory.standard _
  exact exists_Q_map_eq_comp_of_equivalence e H
    (toModuleSheaf.{u} Λ (J.over V) (overRingMap Λ J ρ V)) (J.overMapPullback (ModuleCat.{u} Λ) f)
    (toModuleSheafOverMapIso.{u} Λ J ρ f) ε g s β
    (Q_map_eq_comp_of_mapDerivedCategory (H := H) b₂ s₂ β hβ)

/-- Restriction of `ModuleCat Λ`-valued sheaves along an arrow of the site preserves finite
colimits, being the left adjoint of `CategoryTheory.Functor.sheafAdjunctionCocontinuous`. -/
@[ega "0 4.3.2" "partial"]
local instance preservesFiniteColimits_overMapPullback {W W' : C} (h : W' ⟶ W) :
    PreservesFiniteColimits (J.overMapPullback (ModuleCat.{u} Λ) h) := by
  have := ((Over.map h).sheafAdjunctionCocontinuous (ModuleCat.{u} Λ)
    (J.over W') (J.over W)).leftAdjoint_preservesColimits
  infer_instance

/-- The global form of Stacks 09BE: every morphism `φ : K̲ ⟶ L̲` of `D(C, Λ)` with `K`
perfect agrees, after restriction to the members `U_i` of a covering of `X`, with the restriction
of the constant map `α̲_i` on `C` for some `α_i : K ⟶ L` of `D(Λ)`. The registered statement,
which reads `α̲_i` as the constant map on `C/U_i`, is
`Stacks.ConstantDerivedMap.exists_cover_overPullback_map_eq_overConstantSheaf_map`. -/
theorem exists_cover_overPullback_map_eq_constantSheaf_map
    [HasDerivedCategory.{d} (ModuleCat.{u} Λ)] [HasDerivedCategory.{d'} (Sheaf J (ModuleCat.{u} Λ))]
    [∀ V : C, HasDerivedCategory.{d''} (Sheaf (J.over V) (ModuleCat.{u} Λ))]
    (X : C) {K L : DerivedCategory (ModuleCat.{u} Λ)} (hK : StacksDraft.Perfect.IsPerfect K)
    (φ : (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.obj L) :
    ∃ (ι : Type u) (U : ι → C) (f : ∀ i, U i ⟶ X), Sieve.ofArrows U f ∈ J X ∧
      ∀ i, ∃ α : K ⟶ L,
        (J.overPullback (ModuleCat.{u} Λ) (U i)).mapDerivedCategory.map φ =
          (J.overPullback (ModuleCat.{u} Λ) (U i)).mapDerivedCategory.map
            ((constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.map α) := by
  classical
  obtain ⟨P, a, b, _, _, hfin, hproj, ⟨eK⟩⟩ := hK
  obtain ⟨T, ⟨eL⟩⟩ := Functor.EssSurj.mem_essImage
    (F := DerivedCategory.Q (C := ModuleCat.{u} Λ)) L
  let c := constantSheaf J (ModuleCat.{u} Λ)
  let c' := c.mapHomologicalComplex (ComplexShape.up ℤ)
  let fac := c.mapDerivedCategoryFactors
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : DerivedCategory.Q.obj (c'.obj P) ⟶ DerivedCategory.Q.obj (c'.obj T),
      ψ = fac.inv.app P ≫ c.mapDerivedCategory.map eK.inv ≫ φ ≫ c.mapDerivedCategory.map eL.inv ≫
        fac.hom.app T := ⟨_, rfl⟩
  obtain ⟨W, bb, s, hs, hψ⟩ := DerivedCategory.left_fac ψ
  have hψ' : ψ ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map bb :=
    ((IsIso.comp_inv_eq _).1 hψ.symm).symm
  let G' := (J.overPullback (ModuleCat.{u} Λ) X).mapHomologicalComplex (ComplexShape.up ℤ)
  have : IsIso (DerivedCategory.Q.map (G'.map s)) :=
    isIso_Q_map_mapHomologicalComplex (J.overPullback (ModuleCat.{u} Λ) X) s
  obtain ⟨S, hS, hA⟩ := exists_cover_Q_map_overMapPullback_eq J Λ a b hfin hproj X
    (G'.map bb) (G'.map s)
  have hA' := fun (V : C) (f : V ⟶ X) (hf : S f) =>
    exists_Q_map_overPullback_eq_of_overMapPullback J Λ f bb s (hA f hf)
  choose γ hγ using hA'
  have hsupp := Stacks.SheafOfModules.finite_notIsZero_of_strictlyBounded P a b
  have hB := fun (V : C) (f : V ⟶ X) (hf : S f) =>
    Stacks.ConstantSheaf.exists_cover_overPullback_eq_constantSheaf_mapHomologicalComplex J P T
      hsupp hfin hproj V (γ V f hf)
  choose S' hS' hg using hB
  let R : Sieve X := Sieve.bind S (fun V f hf => S' V f hf)
  have hR : R ∈ J X := J.bind_covering hS (fun V f hf => hS' V f hf)
  refine ⟨{p : Σ Y : C, Y ⟶ X // R p.2}, fun p => p.1.1, fun p => p.1.2,
    J.superset_covering (fun Y k hk => Sieve.ofArrows_mk (fun p : {p : Σ Y : C, Y ⟶ X // R p.2} =>
      p.1.1) (fun p => p.1.2) ⟨⟨Y, k⟩, hk⟩) hR, ?_⟩
  rintro ⟨⟨Y, k⟩, hk⟩
  obtain ⟨Z, h, f, hf, hh, -⟩ := id hk
  change ∃ α : K ⟶ L, (J.overPullback (ModuleCat.{u} Λ) Y).mapDerivedCategory.map φ = _
  obtain ⟨g, hgn⟩ := hg Z f hf h hh
  refine ⟨eK.hom ≫ DerivedCategory.Q.map g ≫ eL.hom, ?_⟩
  have hroof : (J.overPullback (ModuleCat.{u} Λ) Y).mapDerivedCategory.map ψ =
      (J.overPullback (ModuleCat.{u} Λ) Y).mapDerivedCategory.map
        (DerivedCategory.Q.map (c'.map g)) :=
    mapDerivedCategory_map_eq_of_roof (J.overPullback (ModuleCat.{u} Λ) Y) ψ bb s hψ' (c'.map g)
      (Q_map_overPullback_eq_of_overMapPullback J Λ h bb s (γ Z f hf) (hγ Z f hf)
        (c'.map g) hgn)
  have hφ : φ = c.mapDerivedCategory.map eK.hom ≫ fac.hom.app P ≫ ψ ≫ fac.inv.app T ≫
      c.mapDerivedCategory.map eL.hom := by
    rw [hψdef]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      ← Functor.map_comp]
    rw [Iso.inv_hom_id]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  have hα : c.mapDerivedCategory.map (eK.hom ≫ DerivedCategory.Q.map g ≫ eL.hom) =
      c.mapDerivedCategory.map eK.hom ≫ fac.hom.app P ≫ DerivedCategory.Q.map (c'.map g) ≫
        fac.inv.app T ≫ c.mapDerivedCategory.map eL.hom := by
    have hn : c.mapDerivedCategory.map (DerivedCategory.Q.map g) =
        fac.hom.app P ≫ DerivedCategory.Q.map (c'.map g) ≫ fac.inv.app T := by
      rw [← Category.assoc, ← c.mapDerivedCategoryFactors_hom_naturality, Category.assoc,
        Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [Functor.map_comp, Functor.map_comp, hn]
    simp only [Category.assoc]
  rw [hφ, hα]
  simp only [Functor.map_comp, hroof]

section Literal

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable [HasDerivedCategory.{d'} (Sheaf J (ModuleCat.{u} Λ))]
  [∀ V : C, HasDerivedCategory.{d''} (Sheaf (J.over V) (ModuleCat.{u} Λ))]

/-- **The constant complex on a slice site is the restriction of the constant complex.** For an
object `U` of the site, the functor `D(Λ) ⥤ D(C/U, Λ)`, `K ↦ K̲` on `C/U`, is identified with
the composite of `K ↦ K̲` on `C` and restriction to `C/U`. It is induced on derived categories by
`Stacks.ConstantSheaf.overPullbackConstantSheafIso`. -/
noncomputable def overConstantSheafMapDerivedCategoryIso [HasDerivedCategory.{d} (ModuleCat.{u} Λ)]
    (U : C) :
    (constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapDerivedCategory ≅
      (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Stacks.ConstantSheaf.overPullbackConstantSheafIso J (ModuleCat.{u} Λ) U) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **Stacks 09BE.** Let `(C, J)` be a site, `X` an object of `C` (in the source, its final
object), `Λ` a ring, and `K`, `L` objects of `D(Λ)` with `K` perfect. Let `φ : K̲ ⟶ L̲` be a
map in `D(C, Λ)`. There exists a covering `{U_i ⟶ X}` such that `φ|_{U_i}` is equal to
`α̲_i` for some map `α_i : K ⟶ L` in `D(Λ)`.

Here `φ|_{U_i}` is the image of `φ` under the functor `D(C, Λ) ⥤ D(C/U_i, Λ)` induced by
restriction, and `α̲_i` is the map `K̲ ⟶ L̲` of `D(C/U_i, Λ)` induced by the constant sheaf
functor of the slice site `C/U_i`; the two objects `(K̲)|_{U_i}` and `K̲` of `D(C/U_i, Λ)` are
identified by the canonical isomorphism
`Stacks.ConstantDerivedMap.overConstantSheafMapDerivedCategoryIso` (and likewise for `L`), which
is the first conjunct. The second conjunct records the equivalent form `φ|_{U_i} = (α̲_i)|_{U_i}`,
with `α̲_i` the constant map on `C`.

The derived categories `D(Λ)`, `D(C, Λ)` and `D(C/V, Λ)` are taken with arbitrary models
(`HasDerivedCategory` instances, which always exist: `HasDerivedCategory.standard`). The site is
small and the modules live in its universe `u`, the library's standard one-universe convention
for sheaves of modules on a site; the ring is commutative, as are all rings of the Stacks
Project; and the final object `X` of the source is generalized to an arbitrary object. -/
@[stacks 09BE]
theorem exists_cover_overPullback_map_eq_overConstantSheaf_map
    [HasDerivedCategory.{d} (ModuleCat.{u} Λ)]
    (X : C) {K L : DerivedCategory (ModuleCat.{u} Λ)} (hK : StacksDraft.Perfect.IsPerfect K)
    (φ : (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.obj L) :
    ∃ (ι : Type u) (U : ι → C) (f : ∀ i, U i ⟶ X), Sieve.ofArrows U f ∈ J X ∧
      ∀ i, ∃ α : K ⟶ L,
        (J.overPullback (ModuleCat.{u} Λ) (U i)).mapDerivedCategory.map φ =
          (overConstantSheafMapDerivedCategoryIso J Λ (U i)).inv.app K ≫
            (constantSheaf (J.over (U i)) (ModuleCat.{u} Λ)).mapDerivedCategory.map α ≫
              (overConstantSheafMapDerivedCategoryIso J Λ (U i)).hom.app L ∧
        (J.overPullback (ModuleCat.{u} Λ) (U i)).mapDerivedCategory.map φ =
          (J.overPullback (ModuleCat.{u} Λ) (U i)).mapDerivedCategory.map
            ((constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.map α) := by
  obtain ⟨ι, U, f, hU, h⟩ := exists_cover_overPullback_map_eq_constantSheaf_map J Λ X hK φ
  refine ⟨ι, U, f, hU, fun i => ?_⟩
  obtain ⟨α, hα⟩ := h i
  refine ⟨α, ?_, hα⟩
  have hn := (overConstantSheafMapDerivedCategoryIso J Λ (U i)).hom.naturality α
  rw [Functor.comp_map] at hn
  rw [hα, hn, Iso.inv_hom_id_app_assoc]

end Literal

end Transport

end Stacks.ConstantDerivedMap

end
