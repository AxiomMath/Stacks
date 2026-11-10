module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Derived lower shriek undoes an exact fully faithful inverse image computed by resolutions

Let `F ⊣ H` be an adjunction between abelian categories in which `H` is exact and fully faithful,
so that the counit `F ∘ H ⟶ id` is invertible, and let `L` be a left derived functor of `F` on
the unbounded derived categories. If there is a class `P` of objects of the source of `F`
satisfying the hypotheses of Stacks 0794 for `F` — it contains a zero object, is closed under
finite direct sums, every object is a quotient of an object of `P`, and `F` carries a bounded
above acyclic complex with terms in `P` to an acyclic complex — and containing the image of `H`,
then `L ∘ H = id` on the unbounded derived category, for any derived functor of `H`.

This is the formal part of the case `i = 3` of Stacks 08QW: there `F` is lower shriek along
`u₃`, `H` is restriction along `u₃`, and `P` is the class of abelian presheaves whose restriction
to every fibre of `u₃` is acyclic for the point resolution of the fibre.

## Main results

* `StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_map`: an exact functor commuting with
  colimits over `ℕ` carries cellular complexes to cellular complexes.
* `Stacks.ChaoticSite.isIso_app_of_cellular`: the comparison of a left derived functor with the
  underived one is invertible at a `P`-cellular complex.
* `Stacks.ChaoticSite.isIso_app_mapHomotopyCategory_obj`: it is invertible on the image of `H`.
* `Stacks.ChaoticSite.derivedCompositeOfCellularImage`: `G ⋙ L ≅ 𝟭` for any left derived
  functor `L` of `F` and any derived functor `G` of `H`.

## Implementation notes

The comparison `α : Qh ⋙ L ⟶ F ⋙ Qh` is invertible on `P`-cellular complexes because those
form a left derivability structure for `F` (Stacks 0794). The image under `H` of an arbitrary
complex is quasi-isomorphic to the image of a cellular complex for the class of *all* objects of
the target, which `H` carries to a `P`-cellular complex; since `F ∘ H` is the identity up to the
counit, naturality of `α` along that quasi-isomorphism makes `α` invertible on the whole image
of `H`. The conclusion then follows exactly as for an exact left adjoint
(`Stacks.ChaoticSite.derivedCompositeOfExactLeftAdjoint`), with `α` in place of the comparison of
`L` with the degreewise functor.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.UnboundedLeftDerivedFunctor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- An exact functor commuting with colimits over `ℕ` carries a `P'`-cellular complex to a
`P`-cellular complex, as soon as it carries the objects satisfying `P'` to objects satisfying
`P`. -/
lemma isPCellular_map (H : B ⥤ A) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] [HasColimitsOfShape ℕ B] [PreservesColimitsOfShape ℕ H]
    {P' : ObjectProperty B} {P : ObjectProperty A} (hH : ∀ N, P' N → P (H.obj N))
    {S : CochainComplex B ℤ} (hS : IsPCellular P' S) :
    IsPCellular P ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj S) := by
  obtain ⟨Q, g, c, hc, e, hle, hQ, hstage⟩ := hS
  let Hc := H.mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesColimitsOfShape ℕ Hc :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i =>
      preservesColimitsOfShape_of_natIso
        (Iso.refl (HomologicalComplex.eval B (ComplexShape.up ℤ) i ⋙ H) :
          HomologicalComplex.eval B (ComplexShape.up ℤ) i ⋙ H ≅
            Hc ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i)
  let g' : ∀ n : ℕ, Hc.obj (Q n) ⟶ Hc.obj (Q (n + 1)) := fun n => Hc.map (g n)
  let η : Functor.ofSequence g' ⟶ Functor.ofSequence g ⋙ Hc :=
    NatTrans.ofSequence (fun n => 𝟙 _) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let η' : Functor.ofSequence g ⋙ Hc ⟶ Functor.ofSequence g' :=
    NatTrans.ofSequence (fun n => 𝟙 _) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let ηi : Functor.ofSequence g' ≅ Functor.ofSequence g ⋙ Hc :=
    { hom := η, inv := η'
      hom_inv_id := by ext n : 2; exact Category.comp_id _
      inv_hom_id := by ext n : 2; exact Category.comp_id _ }
  let c' : Cocone (Functor.ofSequence g') := (Cocone.precompose ηi.hom).obj (Hc.mapCocone c)
  have hc' : IsColimit c' :=
    (IsColimit.precomposeHomEquiv ηi (Hc.mapCocone c)).symm (isColimitOfPreserves Hc hc)
  refine ⟨fun n => Hc.obj (Q n), g', c', hc', Hc.mapIso e, fun n => ?_, fun n i => hH _ (hQ n i),
    fun n i hi => ?_⟩
  · have := hle n
    dsimp [Hc]
    infer_instance
  · have h := hstage n i hi
    have : c'.ι.app n ≫ (Hc.mapIso e).hom = Hc.map (c.ι.app n ≫ e.hom) := by
      have h1 : η.app n = 𝟙 _ := NatTrans.ofSequence_app _ _ n
      change (η.app n ≫ Hc.map (c.ι.app n)) ≫ Hc.map e.hom = _
      rw [h1]
      exact (congrArg (· ≫ Hc.map e.hom) (Category.id_comp _)).trans (Hc.map_comp _ _).symm
    rw [this]
    exact HomologicalComplex.quasiIsoAt_map_of_preservesHomology _ H i

end StacksDraft.UnboundedLeftDerivedFunctor

namespace Stacks.ChaoticSite

open StacksDraft.UnboundedLeftDerivedFunctor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

omit [HasDerivedCategory B] in
/-- Every object of `K(B)` receives a quasi-isomorphism from the image of a complex which is
cellular for the class of all objects. -/
lemma exists_quasiIso_from_isPCellular_top [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ B] (K : HomotopyCategory B (ComplexShape.up ℤ)) :
    ∃ (S : CochainComplex B ℤ) (_ : IsPCellular ⊤ S)
      (w : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj S ⟶ K),
      HomotopyCategory.quasiIso B (ComplexShape.up ℤ) w := by
  obtain ⟨R⟩ := hasLeftResolutions_cellularLocalizerMorphism (⊤ : ObjectProperty B)
    (fun _ _ _ _ => trivial) (fun X => ⟨X, trivial, 𝟙 X, inferInstance⟩) K
  obtain ⟨S, hS, ⟨e⟩⟩ := R.X₁.property
  refine ⟨S, hS, e.inv ≫ R.w, ?_⟩
  exact (MorphismProperty.RespectsIso.precomp _ e.inv R.w R.hw)


variable {F : A ⥤ B} {H : B ⥤ A} (adj : F ⊣ H) [F.Additive] [H.Additive]
  [PreservesFiniteColimits F] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
  [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ H]
  (P : ObjectProperty A) [P.ContainsZero]
  (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
  (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
  (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
    L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
  (hH : ∀ N : B, P (H.obj N))
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]

include hsum hP hFP in
/-- The comparison of a left derived functor of `F` with `F` is invertible on the objects of
`K(A)` which are `P`-cellular, for a class `P` satisfying the hypotheses of Stacks 0794. -/
lemma isIso_app_of_cellular (X : HomotopyCategory A (.up ℤ)) (hX : cellular P X) :
    IsIso (α.app X) := by
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism P
    (hasLeftResolutions_cellularLocalizerMorphism P hsum hP)
  exact LeftDerivedByResolutions.isIso_app_of_derives (cellularLocalizerMorphism P) _
    (derives_cellularLocalizerMorphism F P hsum hP hFP) DerivedCategory.Qh L α ⟨X, hX⟩

omit [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ A]
  [HasExactColimitsOfShape ℕ B] [PreservesColimitsOfShape ℕ H] in
/-- An exact functor carries quasi-isomorphisms of `K(B)` to quasi-isomorphisms. -/
lemma isIso_Qh_map_mapHomotopyCategory_map {K K' : HomotopyCategory B (.up ℤ)} (w : K ⟶ K')
    (hw : HomotopyCategory.quasiIso B (.up ℤ) w) :
    IsIso (DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map w)) := by
  have : IsIso (DerivedCategory.Qh.map w) := Localization.inverts DerivedCategory.Qh _ w hw
  have h := H.mapDerivedCategoryFactorsh.hom.naturality w
  have h' : DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map w) =
      inv (H.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategory.map (DerivedCategory.Qh.map w) ≫
          H.mapDerivedCategoryFactorsh.hom.app K' := by
    simp only [Functor.comp_map] at h
    rw [h, IsIso.inv_hom_id_assoc]
  rw [h']
  infer_instance

omit [HasDerivedCategory A] [PreservesFiniteColimits F] [PreservesFiniteLimits H]
  [PreservesFiniteColimits H] [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B] [PreservesColimitsOfShape ℕ F]
  [PreservesColimitsOfShape ℕ H] in
include adj in
/-- `F ∘ H` carries quasi-isomorphisms of `K(B)` to quasi-isomorphisms when the counit of `F ⊣ H`
is invertible. -/
lemma isIso_Qh_map_F_H_map [H.Full] [H.Faithful] {K₁ K₂ : HomotopyCategory B (.up ℤ)}
    (w : K₁ ⟶ K₂) (hw : HomotopyCategory.quasiIso B (.up ℤ) w) :
    IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((H.mapHomotopyCategory (.up ℤ)).map w)) := by
  let adjh := adj.mapHomotopyCategory (ComplexShape.up ℤ)
  have hn := adjh.counit.naturality w
  have : IsIso (DerivedCategory.Qh.map w) := Localization.inverts DerivedCategory.Qh _ w hw
  have he : (F.mapHomotopyCategory (.up ℤ)).map ((H.mapHomotopyCategory (.up ℤ)).map w) =
      adjh.counit.app K₁ ≫ w ≫ inv (adjh.counit.app K₂) := by
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  dsimp only [Functor.comp_map]
  rw [he, Functor.map_comp, Functor.map_comp]
  infer_instance

include adj hsum hP hFP hH in
/-- **The comparison of a left derived functor of `F` is invertible on the image of `H`**, when
`H` is fully faithful and exact and carries every object into a class `P` on which `F` is
computed by `P`-cellular resolutions. -/
lemma isIso_app_mapHomotopyCategory_obj [H.Full] [H.Faithful]
    (K : HomotopyCategory B (.up ℤ)) :
    IsIso (α.app ((H.mapHomotopyCategory (.up ℤ)).obj K)) := by
  obtain ⟨S, hS, w, hw⟩ := exists_quasiIso_from_isPCellular_top K
  have hX : cellular P ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient B (.up ℤ)).obj S)) :=
    ⟨_, isPCellular_map H (fun N _ => hH N) hS, ⟨Iso.refl _⟩⟩
  have h₁ := isIso_app_of_cellular P hsum hP hFP L α _ hX
  have h₂ : IsIso ((DerivedCategory.Qh ⋙ L).map ((H.mapHomotopyCategory (.up ℤ)).map w)) := by
    have := isIso_Qh_map_mapHomotopyCategory_map (H := H) w hw
    dsimp only [Functor.comp_map]
    infer_instance
  have h₃ := isIso_Qh_map_F_H_map adj w hw
  have hnat := α.naturality ((H.mapHomotopyCategory (.up ℤ)).map w)
  have h₄ : IsIso ((DerivedCategory.Qh ⋙ L).map ((H.mapHomotopyCategory (.up ℤ)).map w) ≫
      α.app ((H.mapHomotopyCategory (.up ℤ)).obj K)) := by
    rw [hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₂ h₄

include adj hsum hP hFP hH in
/-- **Stacks 08QW, the mechanism of the case `i = 3`.** Let `F ⊣ H` be an adjunction between
abelian categories with `H` exact and fully faithful, and let `P` be a class of objects of `A`
satisfying the hypotheses of Stacks 0794 for `F` and containing the image of `H`. Then any left
derived functor `L` of `F` composed with any derived functor `G` of `H` is the identity. -/
def derivedCompositeOfCellularImage [H.Full] [H.Faithful]
    (G : DerivedCategory B ⥤ DerivedCategory A)
    (e : DerivedCategory.Qh ⋙ G ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  have : ∀ K, IsIso ((Functor.whiskerLeft (H.mapHomotopyCategory (.up ℤ)) α).app K) :=
    fun K => isIso_app_mapHomotopyCategory_obj adj P hsum hP hFP hH L α K
  have : IsIso (Functor.whiskerLeft (H.mapHomotopyCategory (.up ℤ)) α) :=
    NatIso.isIso_of_isIso_app _
  let comm : DerivedCategory.Qh ⋙ (G ⋙ L) ≅ DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory B) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e L ≪≫
    Functor.associator _ _ _ ≪≫
    asIso (Functor.whiskerLeft (H.mapHomotopyCategory (.up ℤ)) α) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit)
      DerivedCategory.Qh ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ)) (DerivedCategory B)).preimageIso comm

section Composite

variable {A B P : Type*} [Category* A] [Category* B] [Category* P] [Abelian A] [Abelian B]
  [Abelian P] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory P]
  {Fg : A ⥤ B} {Hg : B ⥤ A} (adjg : Fg ⊣ Hg)
  {Fπ : A ⥤ P} {Hπ : P ⥤ A} (adjπ : Fπ ⊣ Hπ)
  {Fi : B ⥤ P} {Hi : P ⥤ B} (adji : Fi ⊣ Hi)
  [Fg.Additive] [Hg.Additive] [Fπ.Additive] [Hπ.Additive] [Fi.Additive] [Hi.Additive]
  [PreservesFiniteLimits Hg] [PreservesFiniteColimits Hg]
  [PreservesFiniteLimits Hπ] [PreservesFiniteColimits Hπ]
  [PreservesFiniteLimits Hi] [PreservesFiniteColimits Hi]
  [PreservesFiniteColimits Fg] [PreservesFiniteColimits Fπ] [PreservesFiniteColimits Fi]
  [EnoughProjectives A] [EnoughProjectives B]
  [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ P]
  [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ P]
  [PreservesColimitsOfShape ℕ Fg] [PreservesColimitsOfShape ℕ Fπ] [PreservesColimitsOfShape ℕ Fi]

include adjg adjπ adji in
/-- **The second half of Stacks 08QW, formally.** Let `g : A → B` and `πᵢ : B → P` be such that
`π⁻¹ = g⁻¹ ∘ πᵢ⁻¹`, with exact inverse images and lower shrieks left adjoint to them, and suppose
`Lg_! ∘ g⁻¹ = id` for some left derived functor of `g_!`. Then for any left derived functors
`Lπ_!` and `Lπᵢ_!`, `Lπ_! ∘ g⁻¹ = Lπᵢ_!`: the derived adjunctions identify `Lπ_!` with
`Lπᵢ_! ∘ Lg_!`, the left adjoint of `g⁻¹ ∘ πᵢ⁻¹`. -/
def derivedLowerShriekCompInverseImageIso (eH : Hπ ≅ Hi ⋙ Hg)
    (Lg : DerivedCategory A ⥤ DerivedCategory B)
    (αg : DerivedCategory.Qh ⋙ Lg ⟶ Fg.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [Lg.IsLeftDerivedFunctor αg (HomotopyCategory.quasiIso A (.up ℤ))]
    (G : DerivedCategory B ⥤ DerivedCategory A) (hg : G ⋙ Lg ≅ 𝟭 _)
    (L : DerivedCategory A ⥤ DerivedCategory P)
    (α : DerivedCategory.Qh ⋙ L ⟶ Fπ.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (Li : DerivedCategory B ⥤ DerivedCategory P)
    (αi : DerivedCategory.Qh ⋙ Li ⟶ Fi.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [Li.IsLeftDerivedFunctor αi (HomotopyCategory.quasiIso B (.up ℤ))] :
    G ⋙ L ≅ Li :=
  let adjL := CategoryHomology.derivedAdjunctionOfEnoughProjectives adjπ L α
  let adjLi := CategoryHomology.derivedAdjunctionOfEnoughProjectives adji Li αi
  let adjLg := CategoryHomology.derivedAdjunctionOfEnoughProjectives adjg Lg αg
  let eD : Hπ.mapDerivedCategory ≅ Hi.mapDerivedCategory ⋙ Hg.mapDerivedCategory :=
    DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ eH ≪≫
      DerivedCategoryComparisons.mapDerivedCategoryCompIso Hi Hg
  let eL : L ≅ Lg ⋙ Li := (adjL.ofNatIsoRight eD).leftAdjointUniq (adjLg.comp adjLi)
  Functor.isoWhiskerLeft G eL ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight hg Li ≪≫ Functor.leftUnitor Li

end Composite

end Stacks.ChaoticSite

end
