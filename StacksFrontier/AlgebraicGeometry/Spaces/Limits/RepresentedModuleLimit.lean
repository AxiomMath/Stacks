module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendsAlong
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleFunctorPullback

/-!
# Morphisms of modules along a limit of represented affine algebraic spaces

Let `E : J ⥤ (Sch/S)` be a cofiltered system of the big fppf site with affine transition
morphisms whose underlying schemes have an affine limit `c`. A morphism between the inverse images
to `h_{c.pt}` of the comparisons `𝓕^a`, `𝓖^a` of two quasi-coherent modules of finite
presentation on an affine stage `E i` is, at some later stage, the inverse image of a morphism,
read through *any* comparison isomorphism between the iterated inverse images (Stacks 01ZR (2) on
the small étale sites of the represented algebraic spaces). The same holds for quasi-coherent
modules of finite presentation on the site, together with the other two clauses of Stacks 01ZR.

## Main results

* `AlgebraicGeometry.Space.exists_descendsAlong_modulePullback_of_isLimit`: a morphism between
  the inverse images to `h_{c.pt}` of `𝓕^a` and `𝓖^a` is, at some stage, the inverse image of a
  morphism, read through every comparison of iterated inverse images.
* `CategoryTheory.Functor.map_eq_of_comp_iso`, `CategoryTheory.Functor.map_map_eq_of_comp_iso`:
  for `G ∘ R ≅ F ∘ R'`, equal images under `G ∘ R` and under `F` determine each other.
* `AlgebraicGeometry.Space.exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite`:
  a quasi-coherent module of finite presentation on `h_U` is `𝓕^a` for some quasi-coherent `𝓕` of
  finite presentation.
* `AlgebraicGeometry.Space.exists_modulePullback_iso_of_isLimit`: a quasi-coherent module of
  finite presentation on `h_{c.pt}` is the inverse image of one on some `h_{E i}`.
* `AlgebraicGeometry.Space.exists_modulePullback_map_eq_of_isLimit`: two morphisms of
  quasi-coherent modules of finite presentation on `h_{E i}` whose inverse images to `h_{c.pt}`
  agree have equal inverse images to some later stage.
* `AlgebraicGeometry.Space.exists_descendsAlong_modulePullback_of_isLimit'`: a morphism between
  the inverse images to `h_{c.pt}` of quasi-coherent modules of finite presentation on `h_{E i}`
  is, at some stage, the inverse image of a morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS) (c : Cone E)

/-- Affine transition morphisms of `F` give affine transition morphisms of `F ⋙ toScheme`. -/
private theorem isAffineHom_comp_toScheme_map {K : Type u} [Category.{u} K]
    (F : K ⥤ BigFppfOver B S hS)
    [∀ {i j : K} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (F.map e))] :
    ∀ {i j : K} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((F ⋙ BigFppfOver.toScheme B S hS).map e) :=
  fun e => inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B S hS).map (F.map e)))

/-- For a morphism `φ` between the inverse images to `h_{c.pt}` of `𝓕^a` and `𝓖^a`, with `𝓕`,
`𝓖` quasi-coherent of finite presentation on the affine stage `E i`, and an affine limit `c.pt`,
there is a transition `e : j ⟶ i` such that `φ` is the inverse image of a morphism over
`h_{E j}`, read through every comparison of iterated inverse images. -/
theorem exists_descendsAlong_modulePullback_of_isLimit
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i : J)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))]
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (E.obj i)).ringCatSheaf).FullSubcategory)
    [M.obj.IsFinitePresentation] [N.obj.IsFinitePresentation]
    (φ : (modulePullback B S hS (schemeSpaceMap (c.π.app i))).obj
        ((representedModuleFunctor B S hS (E.obj i)).obj M) ⟶
      (modulePullback B S hS (schemeSpaceMap (c.π.app i))).obj
        ((representedModuleFunctor B S hS (E.obj i)).obj N)) :
    ∃ (j : J) (e : j ⟶ i),
      ∀ κ : (representedModuleFunctor B S hS (E.obj i) ⋙
          modulePullback B S hS (schemeSpaceMap (E.map e))) ⋙
            modulePullback B S hS (schemeSpaceMap (c.π.app j)) ≅
          representedModuleFunctor B S hS (E.obj i) ⋙
            modulePullback B S hS (schemeSpaceMap (c.π.app i)),
        Functor.DescendsAlong κ φ := by
  have := @isAffineHom_comp_toScheme_map B S hS J _ E _
  have : IsAffine ((BigFppfOver.toScheme B S hS).mapCone c).pt :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
  have : IsAffine ((E ⋙ BigFppfOver.toScheme B S hS).obj i) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  let RF := representedModuleFunctorFullyFaithful B S hS c.pt
  let βi := representedModuleFunctorPullbackIso B S hS (c.π.app i)
  obtain ⟨j, e, hZ⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_descendsAlong_pullbackQcoh_of_isLimit
      (E ⋙ BigFppfOver.toScheme B S hS) ((BigFppfOver.toScheme B S hS).mapCone c) hc i M N
      (RF.preimage (βi.inv.app M ≫ φ ≫ βi.hom.app N))
  exact ⟨j, e, Functor.DescendsAlong.transport RF
    (representedModuleFunctorPullbackIso B S hS (E.map e))
    (representedModuleFunctorPullbackIso B S hS (c.π.app j)) βi φ hZ⟩

section Aux

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']

/-- Equal images under `G ∘ R` give equal images under `F`, when `G ∘ R ≅ F ∘ R'` with `R'`
faithful. -/
theorem _root_.CategoryTheory.Functor.map_eq_of_comp_iso {R : C ⥤ D} {G : D ⥤ D'} {F : C ⥤ C'}
    {R' : C' ⥤ D'} [R'.Faithful] (β : R ⋙ G ≅ F ⋙ R') {X Y : C} {f g : X ⟶ Y}
    (h : G.map (R.map f) = G.map (R.map g)) : F.map f = F.map g := by
  apply R'.map_injective
  have hf := β.inv.naturality f
  have hg := β.inv.naturality g
  simp only [Functor.comp_map] at hf hg
  rw [← cancel_mono (β.inv.app Y), hf, hg, h]

/-- Equal images under `F` give equal images under `G ∘ R`, when `G ∘ R ≅ F ∘ R'`. -/
theorem _root_.CategoryTheory.Functor.map_map_eq_of_comp_iso {R : C ⥤ D} {G : D ⥤ D'}
    {F : C ⥤ C'} {R' : C' ⥤ D'} (β : R ⋙ G ≅ F ⋙ R') {X Y : C} {f g : X ⟶ Y}
    (h : F.map f = F.map g) : G.map (R.map f) = G.map (R.map g) := by
  have hf := β.hom.naturality f
  have hg := β.hom.naturality g
  simp only [Functor.comp_map] at hf hg
  rw [← cancel_mono (β.hom.app Y), hf, hg, h]

end Aux


variable {B S hS} in
/-- A quasi-coherent module of finite presentation on `h_U` is `𝓕^a` for a quasi-coherent `𝓕`
of finite presentation on the scheme underlying `U`. -/
theorem exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite
    (U : BigFppfOver B S hS)
    (G : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2) (hG : G.IsQuasicoherentOnSite)
    (hGfp : G.IsFinitePresentationOnSite) :
    ∃ M, M.obj.IsFinitePresentation ∧
      Nonempty ((representedModuleFunctor B S hS U).obj M ≅ G) := by
  obtain ⟨M, ⟨a⟩⟩ := exists_representedModuleFunctor_iso B S hS U G hG
  exact ⟨M, isFinitePresentation_of_isFinitePresentationOnSite_representedModuleFunctor_obj B S hS
    U M (SheafOfModules.IsFinitePresentationOnSite.of_iso a.symm hGfp), ⟨a⟩⟩

end AlgebraicGeometry.Space

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS) (c : Cone E)

private theorem exists_pullbackQcoh_iso_aux
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((E ⋙ BigFppfOver.toScheme B S hS).map e)]
    [∀ j, CompactSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj j)]
    [∀ j, QuasiSeparatedSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj j)]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj c.pt).ringCatSheaf).FullSubcategory)
    [N.obj.IsFinitePresentation] :
    ∃ (i : J) (M : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj (E.obj i)).ringCatSheaf).FullSubcategory),
      M.obj.IsFinitePresentation ∧
        Nonempty ((Stacks.Modules.pullbackQcoh
          ((BigFppfOver.toScheme B S hS).map (c.π.app i))).obj M ≅ N) :=
  Stacks.AlgebraicGeometry.ModuleLimits.exists_pullbackQcoh_iso_of_isLimit
    (E ⋙ BigFppfOver.toScheme B S hS) ((BigFppfOver.toScheme B S hS).mapCone c) hc N

private theorem exists_pullbackQcoh_map_eq_aux
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((E ⋙ BigFppfOver.toScheme B S hS).map e)]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i : J)
    [CompactSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj i)]
    {M N : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj (E.obj i)).ringCatSheaf).FullSubcategory}
    [M.obj.IsFinitePresentation] [N.obj.IsFinitePresentation] (ψ₁ ψ₂ : M ⟶ N)
    (h : (Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (c.π.app i))).map ψ₁ =
      (Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (c.π.app i))).map ψ₂) :
    ∃ (j : J) (e : j ⟶ i),
      (Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (E.map e))).map ψ₁ =
        (Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (E.map e))).map ψ₂ :=
  Stacks.AlgebraicGeometry.ModuleLimits.exists_pullbackQcoh_map_eq_of_isLimit
    (E ⋙ BigFppfOver.toScheme B S hS) ((BigFppfOver.toScheme B S hS).mapCone c) hc i ψ₁ ψ₂ h


private theorem exists_modulePullback_iso_of_isLimit_aux
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    [∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j))]
    [∀ j, QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (G : Modules.{u, u} B S hS (schemeSpace c.pt).1 (schemeSpace c.pt).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite) :
    ∃ (i : J) (Gᵢ : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2),
      Gᵢ.IsQuasicoherentOnSite ∧ Gᵢ.IsFinitePresentationOnSite ∧
        Nonempty ((modulePullback B S hS (schemeSpaceMap (c.π.app i))).obj Gᵢ ≅ G) := by
  have := @isAffineHom_comp_toScheme_map B S hS J _ E _
  have : ∀ j, CompactSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj j) := fun j =>
    inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
  have : ∀ j, QuasiSeparatedSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj j) := fun j =>
    inferInstanceAs (QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
  obtain ⟨N, hN, ⟨a⟩⟩ :=
    exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite c.pt G hG hGfp
  obtain ⟨i, M, hM, ⟨b⟩⟩ := exists_pullbackQcoh_iso_aux B S hS E c hc N
  exact ⟨i, (representedModuleFunctor B S hS (E.obj i)).obj M,
    ((representedQuasicoherentSchemeEquivalence B S hS (E.obj i)).functor.obj M).property,
    isFinitePresentationOnSite_representedModuleFunctor_obj B S hS (E.obj i) M,
    ⟨(representedModuleFunctorPullbackIso B S hS (c.π.app i)).app M ≪≫
      (representedModuleFunctor B S hS c.pt).mapIso b ≪≫ a⟩⟩

private theorem exists_modulePullback_map_eq_of_isLimit_aux
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i : J)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj i))]
    {G H : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite) (ψ₁ ψ₂ : G ⟶ H)
    (h : (modulePullback B S hS (schemeSpaceMap (c.π.app i))).map ψ₁ =
      (modulePullback B S hS (schemeSpaceMap (c.π.app i))).map ψ₂) :
    ∃ (j : J) (e : j ⟶ i), (modulePullback B S hS (schemeSpaceMap (E.map e))).map ψ₁ =
      (modulePullback B S hS (schemeSpaceMap (E.map e))).map ψ₂ := by
  have := @isAffineHom_comp_toScheme_map B S hS J _ E _
  have : CompactSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj i) :=
    inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  obtain ⟨M, hM, ⟨a⟩⟩ :=
    exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite (E.obj i) G hG hGfp
  obtain ⟨N, hN, ⟨b⟩⟩ :=
    exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite (E.obj i) H hH hHfp
  let R := representedModuleFunctor B S hS (E.obj i)
  let RF := representedModuleFunctorFullyFaithful B S hS (E.obj i)
  have : (representedModuleFunctor B S hS c.pt).Faithful :=
    (representedModuleFunctorFullyFaithful B S hS c.pt).faithful
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, R.map f₁ = a.hom ≫ ψ₁ ≫ b.inv := ⟨_, RF.map_preimage _⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f₂, R.map f₂ = a.hom ≫ ψ₂ ≫ b.inv := ⟨_, RF.map_preimage _⟩
  have h₁ : (modulePullback B S hS (schemeSpaceMap (c.π.app i))).map (R.map f₁) =
      (modulePullback B S hS (schemeSpaceMap (c.π.app i))).map (R.map f₂) := by
    simp only [hf₁, hf₂, Functor.map_comp, h]
  have hZ := Functor.map_eq_of_comp_iso (R := R)
    (G := modulePullback B S hS (schemeSpaceMap (c.π.app i)))
    (F := Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (c.π.app i)))
    (R' := representedModuleFunctor B S hS c.pt)
    (representedModuleFunctorPullbackIso B S hS (c.π.app i)) h₁
  obtain ⟨j, e, he⟩ := exists_pullbackQcoh_map_eq_aux B S hS E c hc i f₁ f₂ hZ
  refine ⟨j, e, ?_⟩
  have h₂ := Functor.map_map_eq_of_comp_iso (R := R)
    (G := modulePullback B S hS (schemeSpaceMap (E.map e)))
    (F := Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map (E.map e)))
    (R' := representedModuleFunctor B S hS (E.obj j))
    (representedModuleFunctorPullbackIso B S hS (E.map e)) he
  simp only [hf₁, hf₂, Functor.map_comp] at h₂
  let F := modulePullback B S hS (schemeSpaceMap (E.map e))
  exact (Iso.cancel_iso_inv_right _ _ (F.mapIso b)).1
    ((Iso.cancel_iso_hom_left (F.mapIso a) _ _).1 h₂)

private theorem exists_descendsAlong_modulePullback_of_isLimit_aux'
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i : J)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))]
    {G H : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (schemeSpaceMap (c.π.app i))).obj G ⟶
      (modulePullback B S hS (schemeSpaceMap (c.π.app i))).obj H) :
    ∃ (j : J) (e : j ⟶ i),
      ∀ κ : modulePullback B S hS (schemeSpaceMap (E.map e)) ⋙
          modulePullback B S hS (schemeSpaceMap (c.π.app j)) ≅
          modulePullback B S hS (schemeSpaceMap (c.π.app i)),
        Functor.DescendsAlong κ φ := by
  obtain ⟨M, hM, ⟨a⟩⟩ :=
    exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite (E.obj i) G hG hGfp
  obtain ⟨N, hN, ⟨b⟩⟩ :=
    exists_representedModuleFunctor_iso_of_isFinitePresentationOnSite (E.obj i) H hH hHfp
  let Fi := modulePullback B S hS (schemeSpaceMap (c.π.app i))
  obtain ⟨j, e, hd⟩ := exists_descendsAlong_modulePullback_of_isLimit B S hS E c hc i M N
    (Fi.map a.hom ≫ φ ≫ Fi.map b.inv)
  refine ⟨j, e, fun κ => ?_⟩
  exact Functor.DescendsAlong.of_iso (Fe := modulePullback B S hS (schemeSpaceMap (E.map e)))
    (Fj := modulePullback B S hS (schemeSpaceMap (c.π.app j))) (Fi := Fi) κ
    (M := (representedModuleFunctor B S hS (E.obj i)).obj M) (M' := G)
    (N := (representedModuleFunctor B S hS (E.obj i)).obj N) (N' := H) a b (φ := φ)
    (Functor.DescendsAlong.of_whiskerLeft (representedModuleFunctor B S hS (E.obj i)) κ (hd _))

end AlgebraicGeometry.Space

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS) (c : Cone E)

/-- For a cofiltered system of quasi-compact quasi-separated schemes with affine transition
morphisms and a limit, a quasi-coherent module of finite presentation on `h_{c.pt}` is the inverse
image of one on some `h_{E i}`. -/
alias exists_modulePullback_iso_of_isLimit := exists_modulePullback_iso_of_isLimit_aux

/-- Two morphisms of quasi-coherent modules of finite presentation on `h_{E i}`, for a
quasi-compact stage, whose inverse images to `h_{c.pt}` agree have equal inverse images to some
later stage. -/
alias exists_modulePullback_map_eq_of_isLimit := exists_modulePullback_map_eq_of_isLimit_aux

/-- For affine `c.pt` and `E i`, a morphism `φ` between the inverse images to `h_{c.pt}` of
quasi-coherent modules of finite presentation on `h_{E i}` is, for some transition `e : j ⟶ i`,
the inverse image of a morphism over `h_{E j}`, read through every comparison of iterated inverse
images. -/
alias exists_descendsAlong_modulePullback_of_isLimit' := exists_descendsAlong_modulePullback_of_isLimit_aux'

end AlgebraicGeometry.Space

end
