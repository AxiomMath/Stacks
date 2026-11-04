module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsRestrict
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictSupported
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodRestriction

/-!
# The comparison map of Stacks 0EIV at a member `V` of `𝒱`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the open
subschemes of `U` containing `U ∩ V(I)`. For `V ∈ 𝒱` and coherent `𝒪_V`-modules `G`, `F`,
Stacks 0EIV considers the canonical map

`colim_{V' ≥ V} Hom_{V'}(G|_{V'}, F|_{V'}) ⟶ Hom_{Coh(V, I𝒪_V)}(G^∧, F^∧)`,

which sends the germ of a morphism to its completion. This file defines that map.

The completion of a morphism `s : G|_{V'} ⟶ F|_{V'}` defined only on `V' ⊆ V` is a morphism on
`V` because restriction from `V` to `V'` is fully faithful on coherent adic systems along
`I 𝒪_V`, whose terms are supported in `U ∩ V(I) ⊆ V'`
(`Stacks.Algebraization.bijective_whiskerRight_restrict_coherentAdicSystems`). The completion is
pinned down sectionwise by `Stacks.Algebraization.IsCompletionOfSection`: on every open `T ⊆ V'`,
the composite `G ⟶ G / I^(n+1) G ⟶ F / I^(n+1) F` is `s` followed by `F ⟶ F / I^(n+1) F`.

## Main definitions

* `Stacks.Algebraization.IsCompletionOfSection` — `φ : G^∧ ⟶ F^∧` is the completion of a section
  `s` of `SheafHom(G, F)` over an open `O`.
* `Stacks.Algebraization.sectionsNearVanishingOn` — the diagram `V' ↦ Γ(V', H)` over the members
  `V' ⊆ V` of `𝒱`.
* `Stacks.Algebraization.nbhdHomComparisonOn` — **the map of Stacks 0EIV at `V`**.

## Main results

* `Stacks.Algebraization.IsCompletionOfSection.unique` and
  `Stacks.Algebraization.exists_isCompletionOfSection` — over an open containing the support of the
  ideal, the completion of a section exists and is unique.
* `Stacks.Algebraization.isCompletionOfSection_nbhdHomComparison` — at `V = U` the library's
  `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` takes a germ to the completion of a
  representative, by `Stacks.Algebraization.restrict_completionProjection_comp_nbhdHomComparison`.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- Every open of `X` inside `O` is the image of an open of the scheme `O`. -/
private theorem exists_image_ι_eq {X : Scheme.{u}} (O : X.Opens) {T : X.Opens} (hT : T ≤ O) :
    ∃ T' : O.toScheme.Opens, O.ι ''ᵁ T' = T :=
  ⟨O.ι ⁻¹ᵁ T, by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hT⟩

/-- Equal morphisms of modules agree on sections. -/
private theorem modules_hom_app_apply_congr {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N}
    (h : f = g) (T : X.Opens) (x : Γ(M, T)) :
    Scheme.Modules.Hom.app f T x = Scheme.Modules.Hom.app g T x :=
  ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f T) h) x

/-- **`φ` is the completion of the section `s`.** For a section `s` of `SheafHom(G, F)` over an
open `O`, a morphism `φ : G^∧ ⟶ F^∧` is its completion when, for every `n` and every open
`T ⊆ O`, the composite `G ⟶ G / I^(n+1) G ⟶ F / I^(n+1) F` agrees on `T` with `s` followed by
`F ⟶ F / I^(n+1) F`. -/
abbrev IsCompletionOfSection (O : X.Opens)
    (s : ((sheafHomFunctor X (coherentObj G)).obj F.obj).val.obj (op O))
    (φ : (completionFunctor X J).obj G ⟶ (completionFunctor X J).obj F) : Prop :=
  ∀ (n : ℕ) (T : X.Opens) (hT : T ≤ O) (x : Γ(G.obj, T)),
    Scheme.Modules.Hom.app (X := X) (completionProjection X J G n ≫ φ.hom.app (op n)) T x =
      Scheme.Modules.Hom.app (X := X) (completionProjection X J F n) T
        (s.app (op (Over.mk (homOfLE hT))) x)

/-- The completion of a section is also the completion of its restriction to a smaller open. -/
theorem IsCompletionOfSection.mono {O O' : X.Opens} (h : O' ≤ O)
    {s : ((sheafHomFunctor X (coherentObj G)).obj F.obj).val.obj (op O)}
    {φ : (completionFunctor X J).obj G ⟶ (completionFunctor X J).obj F}
    (hs : IsCompletionOfSection J G F O s φ) :
    IsCompletionOfSection J G F O'
      (((sheafHomFunctor X (coherentObj G)).obj F.obj).val.map (homOfLE h).op s) φ :=
  fun n T hT x => hs n T (hT.trans h) x

/-- **The completion of a section is unique** over an open containing the support of the
ideal: two candidates agree after restriction to that open on every term, and restriction is
injective on morphisms into a module supported in it. -/
theorem IsCompletionOfSection.unique {O : X.Opens} (hO : (J.support : Set X) ⊆ O)
    {s : ((sheafHomFunctor X (coherentObj G)).obj F.obj).val.obj (op O)}
    {φ φ' : (completionFunctor X J).obj G ⟶ (completionFunctor X J).obj F}
    (hφ : IsCompletionOfSection J G F O s φ) (hφ' : IsCompletionOfSection J G F O s φ') :
    φ = φ' := by
  let O' : X.Opens := ⟨(J.support : Set X)ᶜ, J.support.isClosed.isOpen_compl⟩
  have hcov : O ⊔ O' = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    by_cases hx : x ∈ (J.support : Set X)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl (hO hx))
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr hx)
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hz := isZero_restrict_of_idealPowerMultiple_eq_bot J (n.unop + 1)
    (((completionFunctor X J).obj F).obj.obj n)
    (((completionFunctor X J).obj F).property.2.1 n.unop)
    O' disjoint_compl_left
  have hinj := (Scheme.Modules.bijective_restrictFunctor_map_of_isZero_restrict O O' hcov
    G.obj _ hz).1
  refine (@cancel_epi _ _ _ _ _ (completionProjection X J G n.unop)
    (epi_completionProjection X J G n.unop) _ _).1 (hinj ?_)
  ext T' x
  exact (hφ n.unop _ (O.ι_image_le T') x).trans (hφ' n.unop _ (O.ι_image_le T') x).symm

end

section
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The completion of a section exists** over an open `O` containing the support of the ideal:
it is the morphism on `X` whose restriction to `O` is the completion of `s : G|_O ⟶ F|_O`, which
exists because restriction to `O` is fully faithful on coherent adic systems. -/
theorem exists_isCompletionOfSection {O : X.Opens} (hO : (J.support : Set X) ⊆ O)
    (s : ((sheafHomFunctor X (coherentObj G)).obj F.obj).val.obj (op O)) :
    ∃ φ : (completionFunctor X J).obj G ⟶ (completionFunctor X J).obj F,
      IsCompletionOfSection J G F O s φ := by
  let R := Scheme.Modules.restrictFunctor O.ι
  let ŝ : restrictCoherentModules O.ι G ⟶ restrictCoherentModules O.ι F :=
    ObjectProperty.homMk (internalHomRestrictEquiv (coherentObj G) F.obj O s)
  let ψ : ((completionFunctor X J).obj G).obj ⋙ R ⟶ ((completionFunctor X J).obj F).obj ⋙ R :=
    (completionRestrictOpenIso O.ι J G).hom ≫
      ((completionFunctor O.toScheme (J.comap O.ι)).map ŝ).hom ≫
        (completionRestrictOpenIso O.ι J F).inv
  obtain ⟨φ, hφ⟩ := (bijective_whiskerRight_restrict_coherentAdicSystems J O hO _ _).2 ψ
  refine ⟨φ, fun n T hT x => ?_⟩
  obtain ⟨T', rfl⟩ := exists_image_ι_eq O hT
  have hφn : R.map (φ.hom.app (op n)) = ψ.app (op n) := NatTrans.congr_app hφ (op n)
  have hG := completionProjection_comp_completionRestrictOpenIso O.ι J G n
  have hF := completionProjection_comp_completionRestrictOpenIso O.ι J F n
  have hq := completionFunctor_map_quotient O.toScheme (J.comap O.ι) ŝ n
  have key : R.map (completionProjection X J G n ≫ φ.hom.app (op n)) =
      ŝ.hom ≫ R.map (completionProjection X J F n) := by
    have hF' : completionProjection O.toScheme (J.comap O.ι) (restrictCoherentModules O.ι F) n ≫
        (completionRestrictOpenIso O.ι J F).inv.app (op n) =
        R.map (completionProjection X J F n) :=
      (congrArg (· ≫ (completionRestrictOpenIso O.ι J F).inv.app (op n)) hF).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (R.map (completionProjection X J F n) ≫ ·)
            ((completionRestrictOpenIso O.ι J F).hom_inv_id_app (op n))).trans
            (Category.comp_id _)))
    have h4 : completionProjection O.toScheme (J.comap O.ι) (restrictCoherentModules O.ι G) n ≫
        ((completionFunctor O.toScheme (J.comap O.ι)).map ŝ).hom.app (op n) ≫
          (completionRestrictOpenIso O.ι J F).inv.app (op n) =
        ŝ.hom ≫ R.map (completionProjection X J F n) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (completionRestrictOpenIso O.ι J F).inv.app (op n)) hq).trans
          ((Category.assoc _ _ _).trans (congrArg (ŝ.hom ≫ ·) hF')))
    have h3 : R.map (completionProjection X J G n) ≫ ψ.app (op n) =
        completionProjection O.toScheme (J.comap O.ι) (restrictCoherentModules O.ι G) n ≫
          ((completionFunctor O.toScheme (J.comap O.ι)).map ŝ).hom.app (op n) ≫
            (completionRestrictOpenIso O.ι J F).inv.app (op n) :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hG)
    exact (R.map_comp _ _).trans ((congrArg (R.map (completionProjection X J G n) ≫ ·) hφn).trans
      (h3.trans h4))
  exact modules_hom_app_apply_congr key T' x
end

section
open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)

/-- **At `V = U` the comparison map takes a germ to the completion of a representative.** -/
theorem isCompletionOfSection_nbhdHomComparison (W : OpensNearVanishing A I a)
    (s : ToType ((sectionsNearVanishing A I a (internalHomNear A a G F).obj).obj W)) :
    IsCompletionOfSection (idealSheafNearVanishing A I a) G F W.openSet s
      (nbhdHomComparison A I a G F (ConcreteCategory.hom
        (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj) W) s)) := by
  intro n T hT x
  obtain ⟨T', rfl⟩ := exists_image_ι_eq W.openSet hT
  exact modules_hom_app_apply_congr
    (restrict_completionProjection_comp_nbhdHomComparison A I a G F W s n) T' x
end

section
open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms
variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}

/-- Completions of sections are additive. -/
theorem IsCompletionOfSection.add {X : Scheme.{u}} [IsLocallyNoetherian X]
    {J : X.IdealSheafData}
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} {O : X.Opens}
    {s t : ((sheafHomFunctor X (coherentObj G)).obj F.obj).val.obj (op O)}
    {φ ψ : (completionFunctor X J).obj G ⟶ (completionFunctor X J).obj F}
    (hs : IsCompletionOfSection J G F O s φ) (ht : IsCompletionOfSection J G F O t ψ) :
    IsCompletionOfSection J G F O (s + t) (φ + ψ) := by
  intro n T hT x
  refine (modules_hom_app_apply_congr
    (Preadditive.comp_add _ _ _ (completionProjection X J G n) (φ.hom.app (op n))
      (ψ.hom.app (op n))) T x).trans ?_
  exact (congrArg₂ (· + ·) (hs n T hT x) (ht n T hT x)).trans (map_add _ _ _).symm

variable (V : OpensNearVanishing A I a)

/-- The ideal sheaf `I 𝒪_V` on a member `V` of `𝒱`. -/
abbrev idealSheafOn : V.openSet.toScheme.IdealSheafData :=
  (idealSheafNearVanishing A I a).comap V.openSet.ι

/-- The preimage in `V` of a member `W ⊆ V` of `𝒱`: the open `W` of the scheme `V`. -/
abbrev Under.preimageOpen (W : Under V) : V.openSet.toScheme.Opens :=
  V.openSet.ι ⁻¹ᵁ W.right.openSet

omit [IsNoetherianRing A] in
/-- The support of `I 𝒪_V` lies in every member of `𝒱` contained in `V`. -/
theorem support_idealSheafOn_subset (W : Under V) :
    ((idealSheafOn V).support : Set V.openSet.toScheme) ⊆ Under.preimageOpen V W := by
  intro x hx
  rw [idealSheafOn, Scheme.IdealSheafData.support_comap] at hx
  exact W.right.contains_vanishing _ (support_baseIdealSheaf_le I (complementZeroLocus A a).ι hx)

/-- The sections of a module `H` on `V` over the members of `𝒱` contained in `V`: the diagram
whose colimit is `colim_{V' ⊆ V} Γ(V', H)`. -/
def sectionsNearVanishingOn (H : V.openSet.toScheme.Modules) : Under V ⥤ Ab.{u} :=
  Under.forget V ⋙ opensNearVanishingFunctor A I a ⋙
    (TopologicalSpace.Opens.map V.openSet.ι.base).op ⋙ H.presheaf

variable (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)

/-- The completion of a section of `SheafHom(G, F)` over a member `W ⊆ V` of `𝒱`. -/
noncomputable def completionOfSectionOn (W : Under V)
    (s : ((sheafHomFunctor V.openSet.toScheme (coherentObj G)).obj F.obj).val.obj
      (op (Under.preimageOpen V W))) :
    (completionFunctor V.openSet.toScheme (idealSheafOn V)).obj G ⟶
      (completionFunctor V.openSet.toScheme (idealSheafOn V)).obj F :=
  (exists_isCompletionOfSection (idealSheafOn V) G F (support_idealSheafOn_subset V W) s).choose

/-- The defining property of `completionOfSectionOn`. -/
theorem isCompletionOfSection_completionOfSectionOn (W : Under V)
    (s : ((sheafHomFunctor V.openSet.toScheme (coherentObj G)).obj F.obj).val.obj
      (op (Under.preimageOpen V W))) :
    IsCompletionOfSection (idealSheafOn V) G F (Under.preimageOpen V W) s
      (completionOfSectionOn V G F W s) :=
  (exists_isCompletionOfSection (idealSheafOn V) G F (support_idealSheafOn_subset V W)
    s).choose_spec

/-- The completions of sections, as a cocone over the sections near the formal locus. -/
noncomputable def completionOfSectionCocone :
    Cocone (sectionsNearVanishingOn V (internalHomCoherent V.openSet.toScheme G F).obj) where
  pt := AddCommGrpCat.of ((completionFunctor V.openSet.toScheme (idealSheafOn V)).obj G ⟶
      (completionFunctor V.openSet.toScheme (idealSheafOn V)).obj F)
  ι :=
  { app := fun W => AddCommGrpCat.ofHom
      { toFun := fun s => completionOfSectionOn V G F W s
        map_zero' := by
          refine (isCompletionOfSection_completionOfSectionOn V G F W 0).unique _ _ _
            (support_idealSheafOn_subset V W) ?_
          intro n T hT x
          refine (ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f T)
            (Limits.comp_zero (f := completionProjection _ (idealSheafOn V) G n))) x).trans ?_
          exact (map_zero _).symm
        map_add' := fun s t =>
          (isCompletionOfSection_completionOfSectionOn V G F W (s + t)).unique _ _ _
            (support_idealSheafOn_subset V W)
            ((isCompletionOfSection_completionOfSectionOn V G F W s).add
              (isCompletionOfSection_completionOfSectionOn V G F W t)) }
    naturality := fun W₁ W₂ g => by
      ext s
      refine (isCompletionOfSection_completionOfSectionOn V G F W₂ _).unique _ _ _
        (support_idealSheafOn_subset V W₂) ?_
      exact (isCompletionOfSection_completionOfSectionOn V G F W₁ s).mono _ _ _ _ }

/-- **The map of Stacks 0EIV at a member `V` of `𝒱`.** The canonical map from the germs of
morphisms `G|_{V'} ⟶ F|_{V'}` on the members `V' ⊆ V` of `𝒱` to the morphisms `G^∧ ⟶ F^∧` of the
completions along `I 𝒪_V`: a germ goes to the completion of a representative. -/
noncomputable def nbhdHomComparisonOn :
    ToType (colimit (sectionsNearVanishingOn V (internalHomCoherent V.openSet.toScheme G F).obj)) →
      ((completionFunctor V.openSet.toScheme (idealSheafOn V)).obj G ⟶
        (completionFunctor V.openSet.toScheme (idealSheafOn V)).obj F) :=
  ConcreteCategory.hom (colimit.desc _ (completionOfSectionCocone V G F))
end

section
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (V : X.Opens)
  (G' F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf)
  (eG : restrictCoherentModules V.ι G' ≅ G) (eF : restrictCoherentModules V.ι F' ≅ F)

/-- A morphism `φ : G'^∧ ⟶ F'^∧` on `X` and a morphism `ψ : G^∧ ⟶ F^∧` on the open `V`
correspond when `ψ` is the restriction of `φ`, read through `G'|_V ≅ G` and `F'|_V ≅ F`. -/
def IsRestrictionOfCompletionHom
    (φ : (completionFunctor X J).obj G' ⟶ (completionFunctor X J).obj F')
    (ψ : (completionFunctor V.toScheme (J.comap V.ι)).obj G ⟶
      (completionFunctor V.toScheme (J.comap V.ι)).obj F) : Prop :=
  Functor.whiskerRight φ.hom (Scheme.Modules.restrictFunctor V.ι) ≫
      (completionRestrictOpenIso V.ι J F').hom ≫
        ((completionFunctor V.toScheme (J.comap V.ι)).map eF.hom).hom =
    (completionRestrictOpenIso V.ι J G').hom ≫
      ((completionFunctor V.toScheme (J.comap V.ι)).map eG.hom).hom ≫ ψ.hom

/-- **Restriction carries completions of sections to completions of sections.** If `ψ` is the
restriction of `φ` to `V` and `φ` is the completion of `s` over `W ⊆ V`, then `ψ` is the
completion of any section `t` over `W ∩ V` that agrees with `s` through `G'|_V ≅ G` and
`F'|_V ≅ F`. -/
theorem IsRestrictionOfCompletionHom.isCompletionOfSection
    {φ : (completionFunctor X J).obj G' ⟶ (completionFunctor X J).obj F'}
    {ψ : (completionFunctor V.toScheme (J.comap V.ι)).obj G ⟶
      (completionFunctor V.toScheme (J.comap V.ι)).obj F}
    (hψ : IsRestrictionOfCompletionHom J V G' F' G F eG eF φ ψ)
    {W : X.Opens} (_hW : W ≤ V)
    (s : ((sheafHomFunctor X (coherentObj G')).obj F'.obj).val.obj (op W))
    (hs : IsCompletionOfSection J G' F' W s φ)
    (t : ((sheafHomFunctor V.toScheme (coherentObj G)).obj F.obj).val.obj (op (V.ι ⁻¹ᵁ W)))
    (ht : ∀ (T : V.toScheme.Opens) (hT : T ≤ V.ι ⁻¹ᵁ W) (y : Γ(G.obj, T)),
      t.app (op (Over.mk (homOfLE hT))) y =
        Scheme.Modules.Hom.app eF.hom.hom T
          (s.app (op (Over.mk (homOfLE ((V.ι.image_mono hT).trans
            (V.ι.image_preimage_le W))))) (Scheme.Modules.Hom.app eG.inv.hom T y))) :
    IsCompletionOfSection (J.comap V.ι) G F (V.ι ⁻¹ᵁ W) t ψ := by
  intro n T hT x
  let R := Scheme.Modules.restrictFunctor V.ι
  let rest := (completionRestrictOpenIso V.ι J F').hom.app (op n) ≫
    ((completionFunctor V.toScheme (J.comap V.ι)).map eF.hom).hom.app (op n)
  have hG := completionProjection_comp_completionRestrictOpenIso V.ι J G' n
  have hF := completionProjection_comp_completionRestrictOpenIso V.ι J F' n
  have hqG := completionFunctor_map_quotient V.toScheme (J.comap V.ι) eG.hom n
  have hqF := completionFunctor_map_quotient V.toScheme (J.comap V.ι) eF.hom n
  -- proj_V(G) = eG.inv ≫ proj_V(G'|V) ≫ (map eG)_n
  have h1 : completionProjection V.toScheme (J.comap V.ι) G n =
      eG.inv.hom ≫
        completionProjection V.toScheme (J.comap V.ι) (restrictCoherentModules V.ι G') n ≫
        ((completionFunctor V.toScheme (J.comap V.ι)).map eG.hom).hom.app (op n) := by
    refine Eq.trans ?_ (congrArg (eG.inv.hom ≫ ·) hqG).symm
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (congrArg (fun f => f.hom) eG.inv_hom_id).symm
  have key : completionProjection V.toScheme (J.comap V.ι) G n ≫ ψ.hom.app (op n) =
      eG.inv.hom ≫ R.map (completionProjection X J G' n ≫ φ.hom.app (op n)) ≫ rest := by
    have hψn' : R.map (φ.hom.app (op n)) ≫ rest =
        (completionRestrictOpenIso V.ι J G').hom.app (op n) ≫
          ((completionFunctor V.toScheme (J.comap V.ι)).map eG.hom).hom.app (op n) ≫
            ψ.hom.app (op n) := NatTrans.congr_app hψ (op n)
    have h2 : completionProjection V.toScheme (J.comap V.ι) (restrictCoherentModules V.ι G') n ≫
        ((completionFunctor V.toScheme (J.comap V.ι)).map eG.hom).hom.app (op n) ≫
          ψ.hom.app (op n) =
        R.map (completionProjection X J G' n ≫ φ.hom.app (op n)) ≫ rest :=
      (congrArg (· ≫ _) hG.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (R.map (completionProjection X J G' n) ≫ ·) hψn'.symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ rest) (R.map_comp _ _).symm))))
    exact (congrArg (· ≫ ψ.hom.app (op n)) h1).trans ((Category.assoc _ _ _).trans
      (congrArg (eG.inv.hom ≫ ·) ((Category.assoc _ _ _).trans h2)))
  have key2 : R.map (completionProjection X J F' n) ≫ rest =
      eF.hom.hom ≫ completionProjection V.toScheme (J.comap V.ι) F n :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hF).trans hqF)
  have e1 := modules_hom_app_apply_congr key T x
  have e2 := modules_hom_app_apply_congr key2 T
    (s.app (op (Over.mk (homOfLE ((V.ι.image_mono hT).trans (V.ι.image_preimage_le W)))))
      (Scheme.Modules.Hom.app eG.inv.hom T x))
  refine e1.trans ?_
  refine (congrArg (Scheme.Modules.Hom.app rest T)
    (hs n _ ((V.ι.image_mono hT).trans (V.ι.image_preimage_le W)) _)).trans ?_
  refine e2.trans ?_
  exact congrArg (Scheme.Modules.Hom.app (completionProjection V.toScheme (J.comap V.ι) F n) T)
    (ht T hT x).symm

/-- The restriction of a morphism of completions on `X` to the open `V`, read through
`G'|_V ≅ G` and `F'|_V ≅ F`. -/
noncomputable def restrictCompletionHom
    (φ : (completionFunctor X J).obj G' ⟶ (completionFunctor X J).obj F') :
    (completionFunctor V.toScheme (J.comap V.ι)).obj G ⟶
      (completionFunctor V.toScheme (J.comap V.ι)).obj F :=
  ObjectProperty.homMk (((completionFunctor V.toScheme (J.comap V.ι)).mapIso eG).inv.hom ≫
    (completionRestrictOpenIso V.ι J G').inv ≫
      Functor.whiskerRight φ.hom (Scheme.Modules.restrictFunctor V.ι) ≫
        (completionRestrictOpenIso V.ι J F').hom ≫
          ((completionFunctor V.toScheme (J.comap V.ι)).map eF.hom).hom)

/-- `restrictCompletionHom` is a restriction in the sense of `IsRestrictionOfCompletionHom`. -/
theorem isRestrictionOfCompletionHom_restrictCompletionHom
    (φ : (completionFunctor X J).obj G' ⟶ (completionFunctor X J).obj F') :
    IsRestrictionOfCompletionHom J V G' F' G F eG eF φ
      (restrictCompletionHom J V G' F' G F eG eF φ) := by
  unfold IsRestrictionOfCompletionHom restrictCompletionHom
  have h : ((completionFunctor V.toScheme (J.comap V.ι)).map eG.hom).hom ≫
      ((completionFunctor V.toScheme (J.comap V.ι)).mapIso eG).inv.hom = 𝟙 _ :=
    congrArg (fun f => f.hom) ((completionFunctor V.toScheme (J.comap V.ι)).mapIso eG).hom_inv_id
  simp only [ObjectProperty.homMk_hom, ← Category.assoc]
  rw [Category.assoc (completionRestrictOpenIso V.ι J G').hom, h, Category.comp_id,
    Iso.hom_inv_id, Category.id_comp]

/-- **Restriction to an open containing the support is bijective on morphisms of completions**,
read through `G'|_V ≅ G` and `F'|_V ≅ F`. -/
theorem bijective_restrictCompletionHom (hV : (J.support : Set X) ⊆ V) :
    Function.Bijective (restrictCompletionHom J V G' F' G F eG eF) := by
  have hc := bijective_whiskerRight_restrict_coherentAdicSystems J V hV
    ((completionFunctor X J).obj G') ((completionFunctor X J).obj F')
  let eL := ((completionFunctor V.toScheme (J.comap V.ι)).mapIso eG).symm
  let eR := (completionFunctor V.toScheme (J.comap V.ι)).mapIso eF
  let conj : (((completionFunctor X J).obj G').obj ⋙ Scheme.Modules.restrictFunctor V.ι ⟶
      ((completionFunctor X J).obj F').obj ⋙ Scheme.Modules.restrictFunctor V.ι) ≃
      ((completionFunctor V.toScheme (J.comap V.ι)).obj G ⟶
        (completionFunctor V.toScheme (J.comap V.ι)).obj F) :=
    { toFun := fun α => ObjectProperty.homMk (eL.hom.hom ≫
        (completionRestrictOpenIso V.ι J G').inv ≫
        α ≫ (completionRestrictOpenIso V.ι J F').hom ≫ eR.hom.hom)
      invFun := fun ψ => (completionRestrictOpenIso V.ι J G').hom ≫ eL.inv.hom ≫ ψ.hom ≫
        eR.inv.hom ≫ (completionRestrictOpenIso V.ι J F').inv
      left_inv := fun α => by
        have h1 : eL.inv.hom ≫ eL.hom.hom = 𝟙 _ := congrArg (fun f => f.hom) eL.inv_hom_id
        have h2 : eR.hom.hom ≫ eR.inv.hom = 𝟙 _ := congrArg (fun f => f.hom) eR.hom_inv_id
        simp only [ObjectProperty.homMk_hom, Category.assoc]
        rw [reassoc_of% h2, Iso.hom_inv_id, Category.comp_id, ← Category.assoc eL.inv.hom,
          h1, Category.id_comp, Iso.hom_inv_id_assoc]
      right_inv := fun ψ => by
        have h1 : eL.hom.hom ≫ eL.inv.hom = 𝟙 _ := congrArg (fun f => f.hom) eL.hom_inv_id
        have h2 : eR.inv.hom ≫ eR.hom.hom = 𝟙 _ := congrArg (fun f => f.hom) eR.inv_hom_id
        refine ObjectProperty.hom_ext _ ?_
        simp only [ObjectProperty.homMk_hom, Category.assoc]
        rw [Iso.inv_hom_id_assoc, reassoc_of% h1]
        exact (congrArg (fun k => ψ.hom ≫ eR.inv.hom ≫ k)
          ((Iso.inv_hom_id_assoc (completionRestrictOpenIso V.ι J F') eR.hom.hom))).trans
          ((congrArg (ψ.hom ≫ ·) h2).trans (Category.comp_id _)) }
  exact conj.bijective.comp hc
end

section
open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms
variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}
  (V : OpensNearVanishing A I a)
  (G' F' : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)
  (eG : restrictCoherentModules V.openSet.ι G' ≅ G)
  (eF : restrictCoherentModules V.openSet.ι F' ≅ F)

/-- **The reduction of Stacks 0EIV from a member `V` of `𝒱` to `U`.** Let `G'`, `F'` be coherent
modules on `U` with `G'|_V ≅ G` and `F'|_V ≅ F`, and let `τ` identify, compatibly with
restriction and with the two isomorphisms, the sections of `SheafHom(G', F')` over each member
`W ⊆ V` of `𝒱` with the sections of `SheafHom(G, F)` over `W` read in `V`. If the comparison map of
Stacks 0EIV at `U` is bijective for `G'`, `F'`, then so is the comparison map at `V` for `G`, `F`.

The two maps differ by the cofinality of `{W ⊆ V}` in `𝒱` and `τ` on the source, and by
restriction to `V` on the target, which is bijective because the terms of the completions are
supported in `U ∩ V(I) ⊆ V`; the square commutes because both ways round a germ goes to the
completion of a representative, which is unique. -/
theorem nbhdHomComparisonOn_bijective_of_sectionsEquiv
    (τ : ∀ W : Under V,
      ToType ((sectionsNearVanishing A I a (internalHomNear A a G' F').obj).obj W.right) ≃+
        ToType ((sectionsNearVanishingOn V (internalHomCoherent V.openSet.toScheme G F).obj).obj W))
    (hres : ∀ {W₁ W₂ : Under V} (g : W₁ ⟶ W₂) s,
      τ W₂ (ConcreteCategory.hom
          ((sectionsNearVanishing A I a (internalHomNear A a G' F').obj).map g.right) s) =
        ConcreteCategory.hom
          ((sectionsNearVanishingOn V (internalHomCoherent V.openSet.toScheme G F).obj).map g)
          (τ W₁ s))
    (hspec : ∀ (W : Under V) s (T : V.openSet.toScheme.Opens) (hT : T ≤ Under.preimageOpen V W)
      (y : Γ(G.obj, T)),
      (τ W s).app (op (Over.mk (homOfLE hT))) y =
        Scheme.Modules.Hom.app eF.hom.hom T
          (s.app (op (Over.mk (homOfLE ((V.openSet.ι.image_mono hT).trans
            (V.openSet.ι.image_preimage_le W.right.openSet)))))
            (Scheme.Modules.Hom.app eG.inv.hom T y)))
    (hΦ : Function.Bijective (nbhdHomComparison A I a G' F')) :
    Function.Bijective (nbhdHomComparisonOn V G F) := by
  have : IsFiltered (Under V) := IsFiltered.under V
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  let HU := (internalHomNear A a G' F').obj
  let HV := (internalHomCoherent V.openSet.toScheme G F).obj
  let N : Under.forget V ⋙ sectionsNearVanishing A I a HU ≅ sectionsNearVanishingOn V HV :=
    NatIso.ofComponents (fun W => (τ W).toAddCommGrpIso) fun {W₁ W₂} g => by
      ext s
      exact hres g s
  let α : colimit (sectionsNearVanishing A I a HU) ≅ colimit (sectionsNearVanishingOn V HV) :=
    (colimitSectionsNearVanishingUnderIso V HU).symm ≪≫ HasColimit.isoOfNatIso N
  have hsupp : ((idealSheafNearVanishing A I a).support : Set _) ⊆ V.openSet := fun x hx =>
    V.contains_vanishing x (support_baseIdealSheaf_le I (complementZeroLocus A a).ι hx)
  let β := restrictCompletionHom (idealSheafNearVanishing A I a) V.openSet G' F' G F eG eF
  have hβ : Function.Bijective β := bijective_restrictCompletionHom _ _ _ _ _ _ eG eF hsupp
  have key : ∀ x, nbhdHomComparisonOn V G F (ConcreteCategory.hom α.hom x) =
      β (nbhdHomComparison A I a G' F' x) := by
    intro x
    obtain ⟨W, t, ht⟩ := Concrete.colimit_exists_rep (sectionsNearVanishingOn V HV)
      (ConcreteCategory.hom α.hom x)
    set s' := (τ W).symm t
    have hx : x = ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a HU) W.right) s' := by
      have h1 : x = ConcreteCategory.hom α.inv (ConcreteCategory.hom α.hom x) :=
        (Iso.hom_inv_id_apply α x).symm
      rw [h1, ← ht]
      show ConcreteCategory.hom ((HasColimit.isoOfNatIso N).inv ≫
        (colimitSectionsNearVanishingUnderIso V HU).hom)
          (ConcreteCategory.hom (colimit.ι (sectionsNearVanishingOn V HV) W) t) = _
      rw [← ConcreteCategory.comp_apply, ← Category.assoc, HasColimit.isoOfNatIso_ι_inv,
        Category.assoc]
      have hfin : colimit.ι (Under.forget V ⋙ sectionsNearVanishing A I a HU) W ≫
          (colimitSectionsNearVanishingUnderIso V HU).hom =
          colimit.ι (sectionsNearVanishing A I a HU) W.right :=
        Functor.Final.ι_colimitIso_hom (Under.forget V) (sectionsNearVanishing A I a HU) W
      rw [hfin]
      rfl
    have hΘ : nbhdHomComparisonOn V G F
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishingOn V HV) W) t) =
        completionOfSectionOn V G F W t := by
      unfold nbhdHomComparisonOn
      rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
      rfl
    have htW : τ W s' = t := (τ W).apply_symm_apply t
    rw [← ht, hΘ, hx]
    refine (isCompletionOfSection_completionOfSectionOn V G F W t).unique _ _ _
      (support_idealSheafOn_subset V W) ?_
    refine (isRestrictionOfCompletionHom_restrictCompletionHom _ V.openSet G' F' G F eG eF
      _).isCompletionOfSection _ V.openSet G' F' G F eG eF W.hom.down s'
      (isCompletionOfSection_nbhdHomComparison A I a G' F' W.right s') t ?_
    intro T hT y
    rw [← htW]
    exact hspec W s' T hT y
  have hfun : nbhdHomComparisonOn V G F =
      β ∘ nbhdHomComparison A I a G' F' ∘ ConcreteCategory.hom α.inv := by
    funext y
    simpa only [Function.comp_apply, Iso.inv_hom_id_apply] using
      key (ConcreteCategory.hom α.inv y)
  rw [hfun]
  exact hβ.comp (hΦ.comp (ConcreteCategory.bijective_of_isIso α.inv))
end

section
variable {X : Scheme.{u}} {G M G₁ M₁ : X.Modules} (eG : G₁ ≅ G) (eM : M ≅ M₁) (O : X.Opens)

/-- Transport of a section of the internal hom along isomorphisms of the source and the target. -/
noncomputable def transportSectionEquiv :
    ((sheafHomFunctor X G).obj M).val.obj (op O) ≃+
      ((sheafHomFunctor X G₁).obj M₁).val.obj (op O) :=
  let Φ := SheafOfModules.overFunctor X.ringCatSheaf O ⋙ SheafOfModules.forget _
  { toEquiv := (Φ.mapIso eG.symm).homCongr (Φ.mapIso eM)
    map_add' := fun σ τ =>
      (congrArg (Φ.map eG.hom ≫ ·) (Preadditive.add_comp _ _ _ σ τ (Φ.map eM.hom))).trans
        (Preadditive.comp_add _ _ _ _ _ _) }

/-- `transportSectionEquiv`, sectionwise. -/
theorem transportSectionEquiv_app (σ : ((sheafHomFunctor X G).obj M).val.obj (op O)) (T : X.Opens)
    (hT : T ≤ O) (y : Γ(G₁, T)) :
    (transportSectionEquiv eG eM O σ).app (op (Over.mk (homOfLE hT))) y =
      Scheme.Modules.Hom.app eM.hom T
        (σ.app (op (Over.mk (homOfLE hT))) (Scheme.Modules.Hom.app eG.hom T y)) :=
  rfl

/-- `transportSectionEquiv` commutes with restriction to a smaller open. -/
theorem transportSectionEquiv_restrict {O₂ : X.Opens} (h : O₂ ≤ O)
    (σ : ((sheafHomFunctor X G).obj M).val.obj (op O)) :
    transportSectionEquiv eG eM O₂ (((sheafHomFunctor X G).obj M).val.map (homOfLE h).op σ) =
      ((sheafHomFunctor X G₁).obj M₁).val.map (homOfLE h).op (transportSectionEquiv eG eM O σ) :=
  rfl
end

end Stacks.Algebraization

end
