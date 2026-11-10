module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ResolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic

/-!
# Leray's acyclicity lemma for `Rf_*`, and base change at a sheaf with no higher direct images

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. This file supplies two building blocks of the proof of
(2) ⟹ (1) in [Stacks, Tag 0A4B].

* **Leray's acyclicity lemma for the unbounded derived direct image.** A bounded below complex
  `K` of abelian sheaves on `X_étale` whose terms are acyclic for `f_*` computes `Rf_*`: the
  derived-functor unit `f_* K ⟶ Rf_* K` is an isomorphism. Acyclicity may be given either as
  `CategoryTheory.Functor.rightAcyclic`, or as the vanishing of the cohomology sheaves
  `H^q(Rf_*(M[0]))`, `q > 0`, of each term `M`; the two are equivalent for any left exact
  functor out of an abelian category with enough injectives in which every complex has a
  K-injective resolution
  (`Stacks.DerivedFunctor.rightAcyclic_iff_isZero_homology_obj_singleFunctor`).
* **Base change at a sheaf with no higher direct images.** If `G` has `H^q(Rf_*(G[0])) = 0` and
  `H^q(Rf'_*((g')^{-1}G[0])) = 0` for `q > 0`, then the derived base change map
  `g^{-1} Rf_* G ⟶ Rf'_* (g')^{-1} G` of
  `Stacks.EtaleCohomology.etaleAbelianSheafDerivedBaseChange` is an isomorphism if and only if
  the underived comparison `g^{-1} f_* G ⟶ f'_* (g')^{-1} G` is.

## Main results

* `Stacks.DerivedFunctor.rightAcyclic_iff_isZero_homology_obj_singleFunctor` — right acyclicity
  is the vanishing of the positive-degree cohomology of an unbounded right derived functor at
  the object placed in degree zero.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic`
  and
  `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_isZero_homology`
  — **Leray's acyclicity lemma** ([Stacks, Tag 015E]) for the unbounded `Rf_*`, in the two
  forms.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_iff` — at a bounded below
  complex whose terms are acyclic for `f_*` and whose inverse images are acyclic for `f'_*`, the
  base change map is invertible exactly when the degreewise comparison is invertible in the
  derived category.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic` — the
  single-sheaf comparison.

## Implementation notes

The generic Leray lemma is `Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`; the étale
statements instantiate it at the unit of `etaleAbelianDerivedDirectImage`.

The single-sheaf comparison reads `etaleAbelianDerivedBaseChange_fac` at the one-term complex
`G[0]`: both units are invertible there by Leray, so the base change map is invertible exactly
when the degreewise comparison at `G[0]` is a quasi-isomorphism, and that comparison is, up to
the identification of `F(G[0])` with `F(G)[0]`, the single functor applied to the underived
comparison at `G`; the single functor into the derived category is fully faithful, so it
reflects isomorphisms.

**Elaboration.** Two points keep the kernel away from the definition of
`etaleAbelianBaseChange`, which is a mate and expensive to unfold. The facts about the degreewise
comparison are proved for a *variable* transformation of the same shape and only instantiated at
the base change comparison (`isIso_comp_mapHomotopyCategory_app_of_baseChangeShape`,
`isIso_Qh_map_comp_mapHomotopyCategory_app_single_iff`). And the sheaf category is written out
in every statement instead of being left to unification: the universe levels unification
assigns are not normalised, and a component `α.app x` compared with `α.app x'` for `x`, `x'`
differing only in the spelling of a universe level is compared by unfolding `α`. For the same
reason the last step of `isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic` elaborates
the single-complex comparison as a `have` before closing the goal with it, rather than against
the goal as expected type.

## References

* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.DerivedFunctor

section RightAcyclic

variable {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

/-- **Right acyclicity read in an unbounded right derived functor.** For a left exact functor
`w : A ⥤ B` out of an abelian category with enough injectives in which every complex has a
K-injective resolution, and a right derived functor `Rw : D(A) ⥤ D(B)` of `w`, an object `M` is
right acyclic for `w` if and only if `H^q(Rw(M[0])) = 0` for every `q > 0`. -/
public theorem rightAcyclic_iff_isZero_homology_obj_singleFunctor
    (w : A ⥤ B) [w.Additive] [PreservesFiniteLimits w]
    (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (M : A) :
    w.rightAcyclic M ↔ ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor B q).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj M))) := by
  rw [rightAcyclic_iff_isZero_rightDerived]
  constructor
  · intro hM q hq
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
    exact (hM p (by exact_mod_cast hq)).of_iso
      ((singleCompDerivedCompHomologyIsoRightDerived w Rw α hres p).app M)
  · intro hM p hp
    exact (hM p (by exact_mod_cast hp)).of_iso
      ((singleCompDerivedCompHomologyIsoRightDerived w Rw α hres p).app M).symm

end RightAcyclic

/-- **The degreewise comparison at a one-term complex.** For a natural transformation
`α : F ⟶ G` of additive functors between abelian categories and an object `M`, the comparison
`F(M[0]) ⟶ G(M[0])` obtained by applying `α` degreewise is an isomorphism of the derived category
if and only if `α.app M` is an isomorphism: up to the identifications `F(M[0]) ≅ F(M)[0]` it is
the single functor applied to `α.app M`, and the single functor into the derived category is
fully faithful. -/
public theorem isIso_Qh_map_natTrans_mapHomotopyCategory_app_single_iff
    {V W : Type*} [Category* V] [Category* W] [Abelian V] [Abelian W] [HasDerivedCategory W]
    {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G) (M : V) :
    IsIso (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor V 0).obj M)))) ↔ IsIso (α.app M) := by
  refine Iff.trans (b := IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor V 0).obj M)))) ?_ ?_
  · rw [DerivedCategory.isIso_Q_map_iff_quasiIso, ← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff, ← DerivedCategory.isIso_Qh_map_iff]
    exact Iff.rfl
  · have e : (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor V 0).obj M) ≫
          (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app M =
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app M ≫
          (CochainComplex.singleFunctor W 0).map (α.app M) := by
      ext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
          HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
          Category.assoc]
        change _ = _ ≫ _ ≫ ((HomologicalComplex.single W (ComplexShape.up ℤ) 0).map
          (α.app M)).f 0
        rw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc, ← Category.assoc,
          ← NatTrans.naturality, Category.assoc]
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (G.obj M) i
          hi).eq_of_tgt _ _
    rw [← isIso_comp_right_iff _ (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app M)),
      ← Functor.map_comp, e, Functor.map_comp, isIso_comp_left_iff]
    refine ⟨fun hα ↦ ?_, fun _ ↦ inferInstance⟩
    have : IsIso ((DerivedCategory.singleFunctor W 0).map (α.app M)) := hα
    exact (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.singleFunctor W 0)).isIso_of_isIso_map (α.app M)

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}}

/-- An abelian sheaf on `X_étale` is right acyclic for `f_*` if and only if its higher direct
images `H^q(Rf_*(M[0]))`, `q > 0`, read in the unbounded derived category, vanish. -/
public theorem rightAcyclic_etaleAbelianDirectImage_iff (f : X ⟶ Y)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDirectImage.{u, v} f).rightAcyclic M ↔ ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj M))) :=
  Stacks.DerivedFunctor.rightAcyclic_iff_isZero_homology_obj_singleFunctor _ _
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective M

/-- **Leray's acyclicity lemma for the unbounded derived direct image** ([Stacks, Tag 015E]).
Let `K` be a bounded below complex of abelian sheaves on `X_étale` each of whose terms is right
acyclic for `f_*`. Then the derived-functor unit `f_* K ⟶ Rf_* K` is an isomorphism of
`D(Y_étale)`. -/
public theorem isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic (f : X ⟶ Y)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (K.X n)) :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K)) :=
  Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic _ _ _ K hK hac

/-- **Leray's acyclicity lemma for the unbounded derived direct image**, with acyclicity of the
terms given as the vanishing of their higher direct images `H^q(Rf_*(K^n[0]))`, `q > 0`. -/
public theorem isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_isZero_homology
    (f : X ⟶ Y)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ (n q : ℤ), 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj (K.X n))))) :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K)) :=
  isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic f K hK fun n ↦
    (rightAcyclic_etaleAbelianDirectImage_iff f (K.X n)).2 (hac n)

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)

/-- The single-complex case, for a variable transformation of the shape of the base change
comparison. -/
private theorem isIso_Qh_map_comp_mapHomotopyCategory_app_single_iff
    (α : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (DerivedCategory.Qh.map (((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G)))) ↔
      IsIso (α.app G) := by
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Functor.map_comp,
    isIso_comp_left_iff, isIso_comp_right_iff]
  exact Stacks.DerivedFunctor.isIso_Qh_map_natTrans_mapHomotopyCategory_app_single_iff α G

/-- **The base change map at a complex with acyclic terms.** Let `K` be a bounded below complex
of abelian sheaves on `X_étale` whose terms are right acyclic for `f_*` and whose inverse images
along `g'` are right acyclic for `f'_*`. Then the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is an isomorphism if and only if the degreewise comparison
`g^{-1} f_* K ⟶ f'_* (g')^{-1} K` is an isomorphism of the derived category: in
`etaleAbelianDerivedBaseChange_fac` the two units are invertible by Leray's lemma and the two
exactness comparisons are invertible. -/
public theorem isIso_etaleAbelianDerivedBaseChange_app_iff
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (K.X n))
    (hac' : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f').rightAcyclic
      ((etaleAbelianInverseImage.{u, v} g').obj (K.X n))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj K))) ↔
      IsIso (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K))) := by
  have h₁ := isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic f K hK hac
  have hK' : CochainComplex.plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    obtain ⟨n, hn⟩ := hK
    exact ⟨n, inferInstance⟩
  have h₂ := isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic f' _ hK' hac'
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)).obj K)
  rw [← isIso_comp_left_iff
      ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
              K)) ≫
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
          ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
            (ComplexShape.up ℤ)).obj K))),
    Category.assoc, hfac]
  have : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
            K))) :=
    h₂
  rw [isIso_comp_right_iff]

/-- The degreewise base change comparison at the one-term complex `G[0]` is an isomorphism of
the derived category if and only if the underived comparison is an isomorphism at `G`. -/
public theorem isIso_Qh_map_etaleAbelianHomotopyBaseChange_app_single_iff
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G)))) ↔
      IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app G) := by
  rw [etaleAbelianHomotopyBaseChange_eq]
  exact isIso_Qh_map_comp_mapHomotopyCategory_app_single_iff f g g' f' _ G

/-- **Base change at a sheaf with no higher direct images.** Let `G` be an abelian sheaf on
`X_étale` with `H^q(Rf_*(G[0])) = 0` and `H^q(Rf'_*((g')^{-1}G[0])) = 0` for all `q > 0`. Then the
base change map `g^{-1} Rf_* G ⟶ Rf'_* (g')^{-1} G` is an isomorphism if and only if the
underived comparison `g^{-1} f_* G ⟶ f'_* (g')^{-1} G` is. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G))))
    (hG' : ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f').obj
          ((etaleAbelianDerivedInverseImage.{u, v} g').obj
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G))))) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G) ↔
      IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app G) := by
  have hG₁ : (etaleAbelianDirectImage.{u, v} f).rightAcyclic G :=
    (rightAcyclic_etaleAbelianDirectImage_iff f G).2 hG
  have hG₂ : (etaleAbelianDirectImage.{u, v} f').rightAcyclic
      ((etaleAbelianInverseImage.{u, v} g').obj G) :=
    (rightAcyclic_etaleAbelianDirectImage_iff f' _).2 fun q hq ↦ (hG' q hq).of_iso
      ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).mapIso
        ((etaleAbelianDerivedDirectImage.{u, v} f').mapIso
        (((etaleAbelianInverseImage.{u, v} g').mapDerivedCategorySingleFunctor 0).app G).symm))
  have hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      ((CochainComplex.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G) :=
    ⟨0, inferInstance⟩
  have e : (DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G)) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app G ≪≫
      ((DerivedCategory.quotientCompQhIso _).app _).symm
  have aux : ∀ (P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
      [P.IsClosedUnderIsomorphisms], (∀ Z, IsZero Z → P Z) → P G → ∀ n : ℤ,
      P (((CochainComplex.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G).X n) := by
    intro P _ hZ hP n
    rcases eq_or_ne n 0 with rfl | hn
    · exact P.prop_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hP
    · exact hZ _ (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn)
  have hac := aux (etaleAbelianDirectImage.{u, v} f).rightAcyclic
    (fun _ hZ ↦ Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _ hZ) hG₁
  have hac' := aux ((etaleAbelianDirectImage.{u, v} f').rightAcyclic.inverseImage
      (etaleAbelianInverseImage.{u, v} g'))
    (fun _ hZ ↦ Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
      ((etaleAbelianInverseImage.{u, v} g').map_isZero hZ)) hG₂
  rw [etaleAbelianSheafDerivedBaseChange, NatTrans.isIso_app_iff_of_iso _ e,
    isIso_etaleAbelianDerivedBaseChange_app_iff f g g' f' h _ hK hac hac']
  have key := isIso_Qh_map_etaleAbelianHomotopyBaseChange_app_single_iff f g g' f' h G
  exact key

end Stacks.EtaleCohomology

end
