module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedHomStage
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulRestrictedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparisonSupplement

/-!
# The Koszul comparison map is an isomorphism on `D_QCoh`

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  For every object `E` of `D_QCoh(𝒪_X)`
the comparison map of [Stacks, Tag 08DC]

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`

is an isomorphism.  This is [Stacks, Tag 08DD].

## Main results

* `Koszul.DerivedSystem.cohomologyComparisonHom_bijective_sheafify` and
  `Koszul.DerivedSystem.cohomologyComparisonHom_bijective`: the comparison into the group of
  morphisms `𝒪_U ⟶ E|_U` is bijective, first for a complex of associated sheaves and then for
  every object of `D_QCoh(𝒪_X)`.
* `Koszul.DerivedSystem.cohomologyComparison_bijective`: the comparison of [Stacks, Tag 08DC]
  into `H⁰(U, E)` is bijective.

## Implementation notes

Both Hom groups live one universe above the ring, so being an isomorphism is expressed as
bijectivity of the underlying map of sets rather than as invertibility in `AddCommGrpCat`.

The proof is the one of the Stacks Project, with the last step made effective.  Writing
`TT(E) = colimₑ Hom_{D(𝒪_X)}(Iₑ, E)`, [Stacks, Tag 08D1] and [Stacks, Tag 08D2] combine with
[Stacks, Tag 0A66] and [Stacks, Tag 06Z0] into an isomorphism `TT(M̃^•) ≅ H⁰(U, M̃^•)`, natural
in the complex `M^•` of `A`-modules — that is the content of
`Koszul.DerivedSystem.koszulHomStageDerivedIso` and
`Koszul.DerivedSystem.koszulHomSectionsIso` — but *not* the comparison map of
[Stacks, Tag 08DC], and the Stacks Project asserts only that some isomorphism exists.

What identifies the two is co-Yoneda.  Every element of `TT(E)` is the image of the class of
`𝟙 : Iₑ ⟶ Iₑ` under a map induced by a morphism out of `Iₑ`, and the comparison map of
[Stacks, Tag 08DC] sends that class to the isomorphism `𝒪_U ≅ Iₑ|_U`.  So any natural family of
maps `TT(-) ⟶ Hom_{D(𝒪_U)}(𝒪_U, (-)|_U)` is the comparison map followed by precomposition with
a single endomorphism `c` of `𝒪_X|_U`, independent of the stage `e` because the maps `Iₑ → 𝒪_X`
form a morphism of systems.  Surjectivity of the isomorphism at `E = 𝒪_X` exhibits a right
inverse for `c`, and
`Koszul.DerivedSystem.isIso_of_comp_eq_id_restrictStructureSheaf` upgrades that to a two-sided
inverse — this is where the argument uses that `𝒪_X|_U` is a sheaf of *commutative* rings in
degree zero, a right-invertible endomorphism of a general object being no isomorphism.
Precomposition with an invertible `c` is bijective, so the comparison map is bijective too.

Running the argument needs the identification only on the objects `M̃^•`, which is where it is
natural; an arbitrary object of `D_QCoh(𝒪_X)` is isomorphic to such an object by
[Stacks, Tag 06Z0], and the comparison map is natural, so bijectivity transports.

## References

* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite

universe u v

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Co-Yoneda: a natural family out of the colimit is the comparison map -/

section Abstract

variable {B : Type*} [Category B] {C : Type*} [Category.{v} C] [Preadditive C]
  {D : Type*} [Category D]

/-- The direct system `n ↦ Hom(Iₙ, X)` of morphism groups out of an inverse system `Ie ⋙ G`. -/
private abbrev homColim (Ie : ℕᵒᵖ ⥤ B) (G : B ⥤ C) (X : C) : ℕ ⥤ AddCommGrpCat.{v} :=
  (Ie ⋙ G).rightOp ⋙ preadditiveYoneda.obj X

/-- **The comparison map out of a colimit of morphism groups is bijective as soon as some family
of bijections is natural.**

The data: a functor `R` (restriction to `U`), an object `O` (the structure sheaf), an inverse
system `Ie ⋙ G` in `C` with a map `a` of systems to the constant system at `O` whose image under
`R` is invertible with inverses `ρ`, a full functor `G` whose image contains `O` up to the
isomorphism `ε`, a family `s` of bijections out of the colimit of the morphism groups at the
objects in the image of `G`, natural in the sense of `sn`, and the comparison family `c`
characterised by `cn`.  The hypothesis `hinvol` is that a one-sided inverse of an endomorphism
of `R O` is two-sided.

The conclusion is that `c` is bijective at every object in the image of `G`. -/
private theorem bijective_of_full_of_natural_equiv (R : C ⥤ D) (G : B ⥤ C) [G.Full]
    (Ie : ℕᵒᵖ ⥤ B) (O : C) (a : (Ie ⋙ G) ⟶ (Functor.const ℕᵒᵖ).obj O)
    (ρ : ∀ n : ℕ, R.obj O ≅ R.obj ((Ie ⋙ G).obj (op n)))
    (hρ : ∀ n : ℕ, (ρ n).inv = R.map (a.app (op n)))
    (M₀ : B) (ε : G.obj M₀ ≅ O)
    (s : ∀ Y : B, ↥(colimit (homColim Ie G (G.obj Y))) ≃ (R.obj O ⟶ R.obj (G.obj Y)))
    (sn : ∀ (Y : B) (n : ℕ) (β : Ie.obj (op n) ⟶ Y),
      s Y (colimit.ι (homColim Ie G (G.obj Y)) n (G.map β)) =
        s (Ie.obj (op n))
            (colimit.ι (homColim Ie G (G.obj (Ie.obj (op n)))) n (𝟙 _)) ≫ R.map (G.map β))
    (c : ∀ X : C, ↥(colimit (homColim Ie G X)) → (R.obj O ⟶ R.obj X))
    (cn : ∀ (X : C) (n : ℕ) (g : (Ie ⋙ G).obj (op n) ⟶ X),
      c X (colimit.ι (homColim Ie G X) n g) = (ρ n).hom ≫ R.map g)
    (hinvol : ∀ h k : R.obj O ⟶ R.obj O, h ≫ k = 𝟙 _ → k ≫ h = 𝟙 _)
    (Y : B) : Function.Bijective (c (G.obj Y)) := by
  let h := s M₀ (colimit.ι (homColim Ie G (G.obj M₀)) 0 (a.app (op 0) ≫ ε.inv)) ≫ R.map ε.hom
  -- the class of `a.app (op n) ≫ ε.inv` is independent of `n`
  have common : ∀ n : ℕ,
      colimit.ι (homColim Ie G (G.obj M₀)) n (a.app (op n) ≫ ε.inv) =
        colimit.ι (homColim Ie G (G.obj M₀)) 0 (a.app (op 0) ≫ ε.inv) := by
    intro n
    have hnat : (Ie ⋙ G).map (homOfLE (Nat.zero_le n)).op ≫ a.app (op 0) = a.app (op n) := by
      simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id] using
        (a.naturality (homOfLE (Nat.zero_le n)).op)
    have hw : colimit.ι (homColim Ie G (G.obj M₀)) n
          ((Ie ⋙ G).map (homOfLE (Nat.zero_le n)).op ≫ a.app (op 0) ≫ ε.inv) =
        colimit.ι (homColim Ie G (G.obj M₀)) 0 (a.app (op 0) ≫ ε.inv) :=
      ConcreteCategory.congr_hom
        (colimit.w (homColim Ie G (G.obj M₀)) (homOfLE (Nat.zero_le n))) _
    rw [← Category.assoc, hnat] at hw
    exact hw
  -- the identity class at stage `n` goes to `h` followed by the restriction isomorphism
  have hid : ∀ n : ℕ, s (Ie.obj (op n))
      (colimit.ι (homColim Ie G (G.obj (Ie.obj (op n)))) n (𝟙 _)) = h ≫ (ρ n).hom := by
    intro n
    obtain ⟨β, hβ⟩ := G.map_surjective (a.app (op n) ≫ ε.inv)
    have hsn := sn M₀ n β
    rw [hβ, common n] at hsn
    have hεinv : R.map (a.app (op n) ≫ ε.inv) = (ρ n).inv ≫ R.map ε.inv := by
      rw [R.map_comp, hρ n]
    rw [hεinv] at hsn
    have hfinal : h = s (Ie.obj (op n))
        (colimit.ι (homColim Ie G (G.obj (Ie.obj (op n)))) n (𝟙 _)) ≫ (ρ n).inv := by
      rw [show h = s M₀ (colimit.ι (homColim Ie G (G.obj M₀)) 0 (a.app (op 0) ≫ ε.inv)) ≫
          R.map ε.hom from rfl, hsn, Category.assoc, Category.assoc, ← R.map_comp,
        ε.inv_hom_id, R.map_id, Category.comp_id]
    rw [hfinal, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- `s` is `h` followed by `c`
  have hs : ∀ (Z : B) (x : ↥(colimit (homColim Ie G (G.obj Z)))),
      s Z x = h ≫ c (G.obj Z) x := by
    intro Z x
    let _ : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
      preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{v})
    obtain ⟨n, α, rfl⟩ := Concrete.colimit_exists_rep (homColim Ie G (G.obj Z)) x
    change (Ie ⋙ G).obj (op n) ⟶ G.obj Z at α
    obtain ⟨β, rfl⟩ := G.map_surjective α
    rw [sn Z n β, cn (G.obj Z) n (G.map β), hid n, Category.assoc]
  -- a right inverse for `h`
  obtain ⟨x₀, hx₀⟩ := (s M₀).surjective (R.map ε.inv)
  have hk : h ≫ c (G.obj M₀) x₀ ≫ R.map ε.hom = 𝟙 _ := by
    rw [← Category.assoc, ← hs M₀ x₀, hx₀, ← R.map_comp, ε.inv_hom_id, R.map_id]
  have kh : (c (G.obj M₀) x₀ ≫ R.map ε.hom) ≫ h = 𝟙 _ := hinvol _ _ hk
  refine ⟨fun b b' hb ↦ (s Y).injective ?_, fun y ↦ ?_⟩
  · rw [hs Y b, hs Y b', hb]
  · obtain ⟨b, hb⟩ := (s Y).surjective (h ≫ y)
    refine ⟨b, ?_⟩
    have hh := congrArg (fun z ↦ (c (G.obj M₀) x₀ ≫ R.map ε.hom) ≫ z) ((hs Y b).symm.trans hb)
    simpa only [← Category.assoc, kh, Category.id_comp] using hh

end Abstract

/-! ### The identification at the complexes of associated sheaves -/

section Sheafify

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-- **The colimit of the morphism groups out of the Koszul system is `H⁰(U, -)` on the complexes
of associated sheaves**, naturally in the object of `D(A)`.  This is
`Koszul.DerivedSystem.koszulHomStageDerivedIso` and
`Koszul.DerivedSystem.koszulHomSectionsIso` with the colimit taken and the result descended along
the localization of the cochain complexes at the quasi-isomorphisms. -/
public def sheafifySectionsIso :
    derivedSheafify A ⋙ homGroupSystemFunctor f ⋙ colim ≅
      derivedSheafify A ⋙ sectionsOnUnion f ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := ModuleCat.{u} A))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ)) AddCommGrpCat.{u + 1}).preimageIso
    ((Functor.isoWhiskerRight (koszulHomStageDerivedIso f) colim).symm ≪≫
      (Functor.isoWhiskerLeft (koszulHomStageFunctor f)
        (preservesColimitNatIso AddCommGrpCat.uliftFunctor.{u + 1, u})).symm ≪≫
      Functor.isoWhiskerRight (koszulHomSectionsIso f) AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- The universe lift of abelian groups is compatible with the identification of `ULift M` with
`M`: the lift of a homomorphism acts on the underlying group as the homomorphism. -/
private lemma ulift_map_apply {M N : AddCommGrpCat.{u}} (φ : M ⟶ N)
    (y : ↥(AddCommGrpCat.uliftFunctor.{u + 1, u}.obj M)) :
    AddEquiv.ulift (AddCommGrpCat.uliftFunctor.{u + 1, u}.map φ y) = φ (AddEquiv.ulift y) :=
  rfl

/-- The identification of `Koszul.DerivedSystem.sheafifySectionsIso`, read as a bijection onto
the group of morphisms `𝒪_U ⟶ M̃^•|_U`. -/
public def sheafifyHomEquiv (M : DerivedCategory (ModuleCat.{u} A)) :
    ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M))) ≃
      ((restrictionToUnion f).obj (structureSheafObject A) ⟶
        (restrictionToUnion f).obj ((derivedSheafify A).obj M)) :=
  ((((sheafifySectionsIso f).app M).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift).trans
    (sectionsEquivOfUnion f ((derivedSheafify A).obj M)).symm).toEquiv

/-- `Koszul.DerivedSystem.sheafifyHomEquiv` sends a class to the morphism `𝒪_U ⟶ M̃^•|_U`
corresponding to its image under `Koszul.DerivedSystem.sheafifySectionsIso`. -/
public lemma sheafifyHomEquiv_apply (M : DerivedCategory (ModuleCat.{u} A))
    (x : ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M)))) :
    sheafifyHomEquiv f M x =
      (sectionsEquivOfUnion f ((derivedSheafify A).obj M)).symm
        (AddEquiv.ulift (((sheafifySectionsIso f).app M).hom x)) :=
  rfl

/-- `Koszul.DerivedSystem.sheafifySectionsIso` is natural in the object of `D(A)`, read on
elements. -/
private lemma sheafifySectionsIso_naturality_apply (M M' : DerivedCategory (ModuleCat.{u} A))
    (β : M ⟶ M') (x : ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M)))) :
    ((sheafifySectionsIso f).app M').hom
        (((homGroupSystemFunctor f ⋙ colim).map ((derivedSheafify A).map β)) x) =
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((sectionsOnUnion f).map ((derivedSheafify A).map β)))
        (((sheafifySectionsIso f).app M).hom x) := by
  have h := ConcreteCategory.congr_hom ((sheafifySectionsIso f).hom.naturality β) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- `Koszul.DerivedSystem.sheafifyHomEquiv`, read as a hypercohomology class over `U`, is the
image of `Koszul.DerivedSystem.sheafifySectionsIso`. -/
private lemma sectionsEquivOfUnion_sheafifyHomEquiv (M : DerivedCategory (ModuleCat.{u} A))
    (x : ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M)))) :
    sectionsEquivOfUnion f ((derivedSheafify A).obj M) (sheafifyHomEquiv f M x) =
      AddEquiv.ulift (((sheafifySectionsIso f).app M).hom x) := by
  rw [sheafifyHomEquiv_apply, AddEquiv.apply_symm_apply]

/-- **`Koszul.DerivedSystem.sheafifyHomEquiv` is natural in the object of `D(A)`.** -/
public lemma sheafifyHomEquiv_naturality (M M' : DerivedCategory (ModuleCat.{u} A))
    (β : M ⟶ M') (x : ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M)))) :
    sheafifyHomEquiv f M'
        (((homGroupSystemFunctor f ⋙ colim).map ((derivedSheafify A).map β)) x) =
      sheafifyHomEquiv f M x ≫ (restrictionToUnion f).map ((derivedSheafify A).map β) := by
  refine (sectionsEquivOfUnion f ((derivedSheafify A).obj M')).injective ?_
  refine Eq.trans ?_ (sectionsEquivOfUnion_naturality f _ _ ((derivedSheafify A).map β)
    (sheafifyHomEquiv f M x)).symm
  refine (sectionsEquivOfUnion_sheafifyHomEquiv f M' _).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun z ↦ ((sectionsOnUnion f).map ((derivedSheafify A).map β)) z)
    (sectionsEquivOfUnion_sheafifyHomEquiv f M x).symm)
  exact (congrArg (fun z ↦ AddEquiv.ulift z)
    (sheafifySectionsIso_naturality_apply f M M' β x)).trans (ulift_map_apply _ _)

/-! ### Bijectivity -/

/-- A one-sided inverse of an endomorphism of `𝒪_X|_U` is two-sided. -/
private lemma restrictStructureSheaf_comp_eq_id_symm
    (h k : (restrictionToUnion f).obj (structureSheafObject A) ⟶
      (restrictionToUnion f).obj (structureSheafObject A)) (hk : h ≫ k = 𝟙 _) :
    k ≫ h = 𝟙 _ := by
  have := isIso_of_comp_eq_id_restrictStructureSheaf f h k hk
  have hkinv : k = CategoryTheory.inv h := by
    rw [← Category.id_comp k, ← IsIso.inv_hom_id h, Category.assoc, hk, Category.comp_id]
  rw [hkinv, IsIso.inv_hom_id]

/-- **The comparison map of [Stacks, Tag 08DC] is bijective at a complex of associated
sheaves.** -/
public theorem cohomologyComparisonHom_bijective_sheafify
    (M : DerivedCategory (ModuleCat.{u} A)) :
    Function.Bijective (cohomologyComparisonHom f ((derivedSheafify A).obj M)) := by
  have hsn : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℕ)
      (β : (koszulCochainDiagram f ⋙ DerivedCategory.Q).obj (op n) ⟶ Y),
      sheafifyHomEquiv f Y (colimit.ι (homGroupSystem f ((derivedSheafify A).obj Y)) n
          ((derivedSheafify A).map β)) =
        sheafifyHomEquiv f ((koszulCochainDiagram f ⋙ DerivedCategory.Q).obj (op n))
            (colimit.ι (homGroupSystem f ((derivedSheafify A).obj
              ((koszulCochainDiagram f ⋙ DerivedCategory.Q).obj (op n)))) n (𝟙 _)) ≫
          (restrictionToUnion f).map ((derivedSheafify A).map β) := by
    intro Y n β
    refine Eq.trans (congrArg (sheafifyHomEquiv f Y) ?_)
      (sheafifyHomEquiv_naturality f _ Y β (colimit.ι (homGroupSystem f
        ((derivedSheafify A).obj
          ((koszulCochainDiagram f ⋙ DerivedCategory.Q).obj (op n)))) n (𝟙 _)))
    have hmap : ((homGroupSystemFunctor f ⋙ colim).map ((derivedSheafify A).map β))
          (colimit.ι (homGroupSystem f ((derivedSheafify A).obj
            ((koszulCochainDiagram f ⋙ DerivedCategory.Q).obj (op n)))) n (𝟙 _)) =
        colimit.ι (homGroupSystem f ((derivedSheafify A).obj Y)) n
          (𝟙 _ ≫ (derivedSheafify A).map β) := by
      have hw := colimit.ι_map (Functor.whiskerLeft (koszulDerivedSystem f).rightOp
        (preadditiveYoneda.map ((derivedSheafify A).map β))) n
      refine Eq.trans (CategoryTheory.comp_apply
        (colimit.ι (homGroupSystem f ((koszulDerivedSystem f).obj (op n))) n)
        ((homGroupSystemFunctor f ⋙ colim).map ((derivedSheafify A).map β))
        (𝟙 ((koszulDerivedSystem f).obj (op n)))).symm ?_
      refine Eq.trans (ConcreteCategory.congr_hom hw
        (𝟙 ((koszulDerivedSystem f).obj (op n)))) ?_
      exact CategoryTheory.comp_apply
        ((Functor.whiskerLeft (koszulDerivedSystem f).rightOp
          (preadditiveYoneda.map ((derivedSheafify A).map β))).app n)
        (colimit.ι (homGroupSystem f ((derivedSheafify A).obj Y)) n)
        (𝟙 ((koszulDerivedSystem f).obj (op n)))
    refine Eq.trans ?_ hmap.symm
    exact congrArg (colimit.ι (homGroupSystem f ((derivedSheafify A).obj Y)) n)
      (Category.id_comp ((derivedSheafify A).map β)).symm
  exact bijective_of_full_of_natural_equiv (restrictionToUnion f) (derivedSheafify A)
    (koszulCochainDiagram f ⋙ DerivedCategory.Q) (structureSheafObject A)
    (koszulSystemToStructureSheaf f) (restrictionIsoOfUnion f) (restrictionIsoOfUnion_inv f)
    (DerivedCategory.Q.obj ((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A))))
    (derivedRingObjectIso A) (sheafifyHomEquiv f) hsn
    (fun X ↦ cohomologyComparisonHom f X) (cohomologyComparisonHom_colimit_ι f)
    (restrictStructureSheaf_comp_eq_id_symm f) M

end Sheafify

/-! ### An arbitrary object of `D_QCoh(𝒪_X)` -/

section QCoh

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-- **The comparison map into the group of morphisms `𝒪_U ⟶ E|_U` is bijective for every object
of `D_QCoh(𝒪_X)`.**  By [Stacks, Tag 06Z0] such an object is isomorphic to a complex of
associated sheaves, where `Koszul.DerivedSystem.cohomologyComparisonHom_bijective_sheafify`
applies, and the comparison map is natural. -/
public theorem cohomologyComparisonHom_bijective (E : derivedCat A)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E) :
    Function.Bijective (cohomologyComparisonHom f E) := by
  obtain ⟨M, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory A E hE
  have biject : ∀ F : derivedCat A ⥤ AddCommGrpCat.{u + 1}, Function.Bijective (F.map e.hom) :=
    fun F ↦ ConcreteCategory.bijective_of_isIso (F.mapIso e).hom
  have hTT := biject (homGroupSystemFunctor f ⋙ colim)
  have hpost := biject (sectionsOnUnionHom f)
  have hnat : ∀ x : ↥(colimit (homGroupSystem f ((derivedSheafify A).obj M))),
      cohomologyComparisonHom f E (((homGroupSystemFunctor f ⋙ colim).map e.hom) x) =
        ((sectionsOnUnionHom f).map e.hom)
          (cohomologyComparisonHom f ((derivedSheafify A).obj M) x) :=
    fun x ↦ cohomologyComparisonHom_naturality f ((derivedSheafify A).obj M) E e.hom x
  refine ⟨fun b b' hb ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hTT.surjective b
    obtain ⟨x', rfl⟩ := hTT.surjective b'
    rw [hnat x, hnat x'] at hb
    exact congrArg ((homGroupSystemFunctor f ⋙ colim).map e.hom)
      ((cohomologyComparisonHom_bijective_sheafify f M).injective (hpost.injective hb))
  · obtain ⟨z, hz⟩ := hpost.surjective y
    obtain ⟨x, hx⟩ := (cohomologyComparisonHom_bijective_sheafify f M).surjective z
    exact ⟨((homGroupSystemFunctor f ⋙ colim).map e.hom) x,
      (hnat x).trans ((congrArg ((sectionsOnUnionHom f).map e.hom) hx).trans hz)⟩

/-- **Stacks 08DD.** In the situation of [Stacks, Tag 08CZ] — `A` a commutative ring, `f` a
finite sequence in `A`, `X = Spec A` and `U = D(f₁) ∪ ⋯ ∪ D(f_r)` — the comparison map of
[Stacks, Tag 08DC]

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`

is an isomorphism for every object `E` of `D_QCoh(𝒪_X)`. -/
@[stacks 08DD]
public theorem cohomologyComparison_bijective (E : derivedCat A)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E) :
    Function.Bijective (cohomologyComparison f E) :=
  (sectionsEquivOfUnion f E).bijective.comp (cohomologyComparisonHom_bijective f E hE)

end QCoh


end Koszul.DerivedSystem

end
