module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftingEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective

/-!
# An affine étale chart of the target through a point of a completion

Let `S` be a scheme contained in a big fppf site `B`, `V = Spec R` a Noetherian affine object of
the site, `T ⊆ |V|` closed, `W` a locally Noetherian formal algebraic space and
`g : V_{/T} ⟶ W` representable by algebraic spaces. For a point `q ∈ T` there are an étale
morphism `f : V' = Spec R' ⟶ V` hitting `q`, a Noetherian adic ring `C₀` with a representable
étale `ψ : Spf C₀ ⟶ W` and a lift `G' : V'_{/f⁻¹T} ⟶ Spf C₀` of the restriction of `g` to `V'`.
This is the reduction step of the proof of Stacks 0GI9 to an affine formal target: an affine
étale chart `W' = Spf C₀` of `W` whose image contains the image of `q`, an affine piece of the
fibre product `V_{/T} ×_W W'` through `q`, and its algebraization by Stacks 0AR4.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_chart_of_isLocallyNoetherian`: the statement
  above.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section of `V'_{/f⁻¹T}` whose image in `V_{/T}` is the section given by `a : U ⟶ V` is the
section given by some `y : U ⟶ V'` with `y ≫ f = a`. -/
theorem exists_presheafSection_eq_of_completionSheafMap_eq {V' V U : BigFppfOver B S hS}
    (f : V' ⟶ V) (Z : Set (Space.points B S hS (yoneda.obj V)))
    (w : (Space.completionSheaf B S hS (yoneda.obj V')
      (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z)).obj.obj (op U))
    (a : U ⟶ V) (ha : Space.HasImageIn B S hS (yoneda.obj V) Z U a)
    (hw : (Space.completionSheafMap B S hS (yoneda.map f) Z).hom.app (op U) w =
      presheafSection (F := yoneda.obj V) B S hS a ha) :
    ∃ (y : U ⟶ V') (hy : Space.HasImageIn B S hS (yoneda.obj V')
        (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z) U y),
      w = presheafSection (F := yoneda.obj V') B S hS y hy ∧ y ≫ f = a := by
  have hV'u : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj V' ⋙ uliftFunctor.{u + 1}) :=
    (upliftedSheaf (yoneda.obj V') (isAlgebraicSpace_yoneda B S hS V')).property
  have hVu : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj V ⋙ uliftFunctor.{u + 1}) :=
    (upliftedSheaf (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).property
  obtain ⟨x, hx⟩ : ∃ x : U ⟶ V', (Space.completionSheafInclusion B S hS (yoneda.obj V') _).hom.app
      (op U) w = ((BigFppfOver.topology B S hS).toSheafify
        (yoneda.obj V' ⋙ uliftFunctor.{u + 1})).app (op U) (ULift.up x) :=
    ⟨_, (toSheafify_ambientRead B S hS hV'u _).symm⟩
  obtain ⟨hxI, hwx⟩ := exists_presheafSection_eq_of_inclusion B S hS
    (isAlgebraicSpace_yoneda B S hS V').isSheaf hV'u w x hx
  refine ⟨x, hxI, hwx, ?_⟩
  have hx' := (hasImageIn_preimage_iff B S hS (yoneda.map f) Z _ _).mp hxI
  have hcs := completionSheafMap_presheafSection (F := yoneda.obj V') (G := yoneda.obj V)
    B S hS (yoneda.map f) Z x hxI hx'
  rw [← hwx, hw] at hcs
  have h := eq_of_presheafSection_eq B S hS hVu hx' ha hcs.symm
  rwa [yoneda_map_app] at h

/-- An isomorphism of sheaves is a left inverse on sections. -/
private theorem iso_inv_app_hom_app_apply {F G : FppfSheaf B S hS} (e : F ≅ G)
    {Z : BigFppfOver B S hS} (t : F.obj.obj (op Z)) :
    e.inv.hom.app (op Z) (e.hom.hom.app (op Z) t) = t :=
  congrFun (congrArg (fun φ => (φ.hom.app (op Z) : _ → _)) e.hom_inv_id) t

/-- A pair of sections of `F` and `G` with the same image in `W` comes from a section of the
fibre product `F ×_W G`. -/
theorem exists_pullback_section_fst_eq {F G W : FppfSheaf B S hS} (a : F ⟶ W) (b : G ⟶ W)
    {Z : BigFppfOver B S hS} (x : F.obj.obj (op Z)) (y : G.obj.obj (op Z))
    (h : a.hom.app (op Z) x = b.hom.app (op Z) y) :
    ∃ σ : (pullback a b).obj.obj (op Z), (pullback.fst a b).hom.app (op Z) σ = x := by
  let J := BigFppfOver.topology B S hS
  have hab : (Sheaf.sectionEquiv J (X := Z) (F := F)).symm x ≫ a =
      (Sheaf.sectionEquiv J (X := Z) (F := G)).symm y ≫ b := by
    apply (Sheaf.sectionEquiv J).injective
    rw [Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, h]
  refine ⟨Sheaf.sectionEquiv J (pullback.lift _ _ hab), ?_⟩
  rw [← Sheaf.sectionEquiv_comp J, pullback.lift_fst, Equiv.apply_symm_apply]

/-- For a locally Noetherian formal algebraic space `W`, a morphism `g : F ⟶ W` and a section
`x` of `F` over `U`, there are an affine `Z ⟶ U` with a point, an affine étale chart
`ψ : Spf C₀ ⟶ W` with `C₀` Noetherian adic, and a section of `F ×_W Spf C₀` over `Z` lifting the
restriction of `x`. -/
theorem exists_pullback_section_of_isLocallyNoetherian {F W : FppfSheaf B S hS}
    (hW : IsLocallyNoetherian B S hS W) (g : F ⟶ W) {U : BigFppfOver B S hS}
    (x : F.obj.obj (op U)) (u : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (Z : BigFppfOver B S hS) (g₁ : Z ⟶ U) (_ : (BigFppfOver.toScheme B S hS).obj Z)
      (C₀ : Type u) (_ : CommRing C₀) (_ : TopologicalSpace C₀) (_ : IsTopologicalRing C₀)
      (_ : IsLinearTopology C₀ C₀) (_ : IsNoetherianRing C₀) (_ : TopologicalRing.IsAdic C₀)
      (E₀ : QuotientSystem B S hS C₀) (ψ : formalSpectrum E₀ ⟶ W)
      (_ : IsRepresentableEtale B S hS ψ) (σ : (pullback g ψ).obj.obj (op Z)),
      (pullback.fst g ψ).hom.app (op Z) σ = F.obj.map g₁.op x := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, Ia, Xa, fa, -, hfa, hsurj, hnoeth⟩ := hW
  obtain ⟨Rs, hRs, hRlift⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc fa hsurj
    (g.hom.app (op U) x)
  obtain ⟨Z₁, g₁, -, hg₁, -, -, ⟨z₁, -⟩⟩ :=
    BigFppfOver.exists_affine_mem_of_mem_topology B S hS hRs u
  obtain ⟨i, t, ht⟩ := hRlift g₁ hg₁
  obtain ⟨-, C₀, _, _, _, _, ⟨-, ⟨P⟩⟩, hCn, hCa⟩ := hnoeth i
  obtain ⟨σ, hσ⟩ := exists_pullback_section_fst_eq B S hS g (P.formalSpectrumIso.inv ≫ fa i)
    (F.obj.map g₁.op x) (P.formalSpectrumIso.hom.hom.app (op Z₁) t) (by
      rw [NatTrans.naturality_apply g.hom g₁.op x, ← ht]
      change _ = (fa i).hom.app _ (P.formalSpectrumIso.inv.hom.app _
        (P.formalSpectrumIso.hom.hom.app _ t))
      rw [iso_inv_app_hom_app_apply])
  exact ⟨Z₁, g₁, z₁, C₀, inferInstance, inferInstance, inferInstance, inferInstance, hCn, hCa,
    P.quotientSystem, _, (isRepresentableEtale_of_isIso B S hS _).comp B S hS (hfa i), σ, hσ⟩

/-- A representable lift `G₀` along `f' : V' ⟶ V` of `g` restricts to a representable lift along
`ι ≫ f'` for any `ι : V'' ⟶ V'`. -/
theorem exists_lift_completionSheafMap_comp {V'' V' V : BigFppfOver B S hS} (ι : V'' ⟶ V')
    (f' : V' ⟶ V) (T : Set (Space.points B S hS (yoneda.obj V))) {X W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj V) T ⟶ W) (ψ : X ⟶ W)
    (G₀ : Space.completionSheaf B S hS (yoneda.obj V')
      (Space.pointsMap B S hS _ (yoneda.map f') ⁻¹' T) ⟶ X)
    (hG₀r : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G₀.hom)
    (hG₀ : Space.completionSheafMap B S hS (yoneda.map f') T ≫ g = G₀ ≫ ψ) :
    ∃ G' : Space.completionSheaf B S hS (yoneda.obj V'')
        (Space.pointsMap B S hS _ (yoneda.map (ι ≫ f')) ⁻¹' T) ⟶ X,
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom ∧
        Space.completionSheafMap B S hS (yoneda.map (ι ≫ f')) T ≫ g = G' ≫ ψ := by
  suffices ∀ (φ : yoneda.obj V'' ⟶ yoneda.obj V), φ = yoneda.map ι ≫ yoneda.map f' →
      ∃ G' : Space.completionSheaf B S hS (yoneda.obj V'')
          (Space.pointsMap B S hS _ φ ⁻¹' T) ⟶ X,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom ∧
          Space.completionSheafMap B S hS φ T ≫ g = G' ≫ ψ from
    this _ (Functor.map_comp _ _ _)
  rintro φ rfl
  have hcomp := Space.completionSheafMap_comp_completionSheafMap (yoneda.map ι)
    (yoneda.map f') T
  refine ⟨eqToHom (congrArg (Space.completionSheaf B S hS _)
    (Space.preimage_pointsMap_preimage_pointsMap (yoneda.map ι) (yoneda.map f') T)).symm ≫
    Space.completionSheafMap B S hS (yoneda.map ι) _ ≫ G₀, ?_, ?_⟩
  · exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (isAdicMorphism_of_isIso B S hS _)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
        (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
          (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) _ _) hG₀r)
  · rw [Category.assoc, Category.assoc, ← hG₀, ← Category.assoc
      (Space.completionSheafMap B S hS (yoneda.map ι) _), hcomp]
    simp

/-- An affine object `Y'` locally of finite type over a Noetherian `affineOver B S hS hR s` with
`s` locally of finite type is isomorphic to some `affineOver B S hS hR' s'` with `R'` Noetherian
and `s'` locally of finite type. -/
theorem exists_isIso_affineOver_of_locallyOfFiniteType {R : Type u} [CommRing R]
    [IsNoetherianRing R] (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s] {Y' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')] (f' : Y' ⟶ affineOver B S hS hR s)
    [hf' : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f')] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsNoetherianRing R') (hR' : B.Contains (Spec (.of R')))
      (s' : Spec (.of R') ⟶ S) (_ : AlgebraicGeometry.LocallyOfFiniteType s')
      (ι : affineOver B S hS hR' s' ⟶ Y'), IsIso ((BigFppfOver.toScheme B S hS).map ι) := by
  have : AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hR s)) :=
    inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)))
  have : AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y') :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map f') }
  obtain ⟨R', _, _, hR', s', ι, hι⟩ := Space.exists_isIso_affineOver Y'
  have hs' : (BigFppfOver.toScheme B S hS).map ι ≫
      (BigFppfOver.toScheme B S hS).map f' ≫ s = s' := by
    have h₁ : (BigFppfOver.toScheme B S hS).map f' ≫ s =
        ((Over.post B.inclusion).obj Y' : Over S).hom := congrArg B.inclusion.map (Over.w f')
    have h₂ : (BigFppfOver.toScheme B S hS).map ι ≫
        ((Over.post B.inclusion).obj Y' : Over S).hom = s' := congrArg B.inclusion.map (Over.w ι)
    rw [h₁, h₂]
  refine ⟨R', inferInstance, inferInstance, hR', s', ?_, ι, hι⟩
  rw [← hs']
  have hιl : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ι) :=
    inferInstance
  exact MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _ hιl
    (MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _ hf'
      ‹AlgebraicGeometry.LocallyOfFiniteType s›)

/-- A representable lift `G₀` of `g` along an étale `f' : Y' ⟶ affineOver B S hS hR s` from an
affine `Y'` gives, through any point `x` of `Y'`, an étale `f` from some
`affineOver B S hS hR' s'` and a representable lift of `g` along `f`. -/
theorem exists_etale_affineOver_lift {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s]
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s))))
    {Y' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    (f' : Y' ⟶ affineOver B S hS hR s)
    [AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f')]
    [AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f')] {X W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T ⟶ W) (ψ : X ⟶ W)
    (G₀ : Space.completionSheaf B S hS (yoneda.obj Y')
      (Space.pointsMap B S hS _ (yoneda.map f') ⁻¹' T) ⟶ X)
    (hG₀r : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G₀.hom)
    (hG₀ : Space.completionSheafMap B S hS (yoneda.map f') T ≫ g = G₀ ≫ ψ)
    (x : (BigFppfOver.toScheme B S hS).obj Y') :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsNoetherianRing R') (hR' : B.Contains (Spec (.of R')))
      (s' : Spec (.of R') ⟶ S) (_ : AlgebraicGeometry.LocallyOfFiniteType s')
      (f : affineOver B S hS hR' s' ⟶ affineOver B S hS hR s)
      (_ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f))
      (v' : PrimeSpectrum R'),
      ((Over.post B.inclusion).map f).left v' = (BigFppfOver.toScheme B S hS).map f' x ∧
      ∃ G' : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR' s'))
          (Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' T) ⟶ X,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom ∧
          Space.completionSheafMap B S hS (yoneda.map f) T ≫ g = G' ≫ ψ := by
  obtain ⟨R', _, _, hR', s', _, ι, hι⟩ :=
    exists_isIso_affineOver_of_locallyOfFiniteType B S hS hR s f'
  obtain ⟨G', hG'r, hG'⟩ := exists_lift_completionSheafMap_comp B S hS ι f' T g ψ G₀ hG₀r hG₀
  have hfE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (ι ≫ f')) := by
    rw [Functor.map_comp]
    infer_instance
  have hinv : (BigFppfOver.toScheme B S hS).map ι
      ((inv ((BigFppfOver.toScheme B S hS).map ι)) x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨R', inferInstance, inferInstance, hR', s', inferInstance, ι ≫ f', hfE,
    (inv ((BigFppfOver.toScheme B S hS).map ι)) x, ?_, G', hG'r, hG'⟩
  change (BigFppfOver.toScheme B S hS).map f' ((BigFppfOver.toScheme B S hS).map ι
    ((inv ((BigFppfOver.toScheme B S hS).map ι)) x)) = _
  rw [hinv]

/-- Stacks 0AR4 applied to an affine Noetherian piece `w : Spf Q ⟶ V_{/T} ×_W X` of the fibre
product: a section `t` of `Spf Q` over `Z` lying over the section given by `a : Z ⟶ V` gives,
through any point `z` of `Z`, an étale `f` from some `affineOver B S hS hR' s'` hitting the image
of `z` and a representable lift of `g` along `f` into `X`. -/
theorem exists_etale_affineOver_lift_of_section {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s]
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s))))
    (hT : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hR s))) T)
    {X W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T ⟶ W)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom) (ψ : X ⟶ W)
    (hfst : IsRepresentableEtale B S hS (pullback.fst g ψ)) {A : Type u} [CommRing A]
    [TopologicalSpace A] {Q : QuotientSystem B S hS A} (w : formalSpectrum Q ⟶ pullback g ψ)
    (hw : IsRepresentableEtale B S hS w)
    (hwaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum Q)) {Z : BigFppfOver B S hS}
    (a : Z ⟶ affineOver B S hS hR s)
    (ha : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hR s)) T Z a)
    (t : (formalSpectrum Q).obj.obj (op Z))
    (ht : (pullback.fst g ψ).hom.app (op Z) (w.hom.app (op Z) t) =
      presheafSection (F := yoneda.obj (affineOver B S hS hR s)) B S hS a ha)
    (z : (BigFppfOver.toScheme B S hS).obj Z) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsNoetherianRing R') (hR' : B.Contains (Spec (.of R')))
      (s' : Spec (.of R') ⟶ S) (_ : AlgebraicGeometry.LocallyOfFiniteType s')
      (f : affineOver B S hS hR' s' ⟶ affineOver B S hS hR s)
      (_ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f))
      (v' : PrimeSpectrum R'),
      ((Over.post B.inclusion).map f).left v' = (BigFppfOver.toScheme B S hS).map a z ∧
      ∃ G' : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR' s'))
          (Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' T) ⟶ X,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom ∧
          Space.completionSheafMap B S hS (yoneda.map f) T ≫ g = G' ≫ ψ := by
  have hgk : IsRepresentableEtale B S hS (w ≫ pullback.fst g ψ) := hw.comp B S hS hfst
  have hYnoeth := isNoetherian_completionSheaf B S hS hR s T hT
  have hWk : IsNoetherian B S hS (formalSpectrum Q) :=
    isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS
      (isLocallyNoetherian_of_isNoetherian B S hS hYnoeth) _ hwaff hgk
  obtain ⟨Y', hY'a, f', e, hf'lft, -, -, he, hf'et⟩ :=
    exists_affine_algebraization_of_isRigEtale B S hS hR s T hT hwaff hWk _
      (isRigEtale_of_isRepresentableEtale B S hS _ hWk hYnoeth hgk)
  have := hY'a
  have := hf'lft
  have := hf'et hgk
  have hxs : (Space.completionSheafMap B S hS (yoneda.map f') T).hom.app (op Z)
      (e.inv.hom.app (op Z) t) =
        presheafSection (F := yoneda.obj (affineOver B S hS hR s)) B S hS a ha := by
    have hinv : e.hom.hom.app (op Z) (e.inv.hom.app (op Z) t) = t :=
      iso_inv_app_hom_app_apply B S hS e.symm t
    rw [← he]
    change (pullback.fst g ψ).hom.app (op Z) (w.hom.app (op Z)
      (e.hom.hom.app (op Z) (e.inv.hom.app (op Z) t))) = _
    rw [hinv, ht]
  obtain ⟨y, -, -, hyf⟩ :=
    exists_presheafSection_eq_of_completionSheafMap_eq B S hS f' T _ a ha hxs
  let G₀ : Space.completionSheaf B S hS (yoneda.obj Y')
      (Space.pointsMap B S hS _ (yoneda.map f') ⁻¹' T) ⟶ X :=
    e.hom ≫ w ≫ pullback.snd g ψ
  have hG₀ : Space.completionSheafMap B S hS (yoneda.map f') T ≫ g = G₀ ≫ ψ := by
    rw [← he]
    simp only [G₀, Category.assoc, pullback.condition]
  have hG₀r : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G₀.hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (isAdicMorphism_of_isIso B S hS e.hom)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hw.1
        (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
          ((IsPullback.of_hasPullback g ψ).map
            (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hg))
  obtain ⟨R', _, _, hR', s', _, f, hfE, v', hv', G', hG'r, hG'⟩ :=
    exists_etale_affineOver_lift B S hS hR s T f' g ψ G₀ hG₀r hG₀
      ((BigFppfOver.toScheme B S hS).map y z)
  refine ⟨R', inferInstance, inferInstance, hR', s', inferInstance, f, hfE, v', hv'.trans ?_, G',
    hG'r, hG'⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hyf]

/-- **An affine étale chart of the target through a point of a completion.** For a Noetherian
affine `V = Spec R`, a closed `T ⊆ |V|`, a locally Noetherian formal algebraic space `W` and
`g : V_{/T} ⟶ W` representable by algebraic spaces, every point `q ∈ T` is the image of a point
of some `V' = Spec R'` étale over `V`, such that the restriction of `g` to `V'_{/f⁻¹T}` lifts to
a representable morphism `G'` into a Noetherian adic formal spectrum `Spf C₀`, representable
étale over `W`. -/
theorem exists_etale_chart_of_isLocallyNoetherian {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s]
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s))))
    (hT : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hR s))) T)
    {W : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W)
    (g : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T ⟶ W)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (q : Space.points B S hS (yoneda.obj (affineOver B S hS hR s))) (hq : q ∈ T) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsNoetherianRing R') (hR' : B.Contains (Spec (.of R')))
      (s' : Spec (.of R') ⟶ S) (_ : AlgebraicGeometry.LocallyOfFiniteType s')
      (f : affineOver B S hS hR' s' ⟶ affineOver B S hS hR s)
      (_ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f))
      (v' : PrimeSpectrum R'),
      ((Over.post B.inclusion).map f).left v' = Space.pointsToScheme B S hS _ q ∧
      ∃ (C₀ : Type u) (_ : CommRing C₀) (_ : TopologicalSpace C₀) (_ : IsTopologicalRing C₀)
        (_ : IsLinearTopology C₀ C₀) (_ : IsNoetherianRing C₀) (_ : TopologicalRing.IsAdic C₀)
        (E₀ : QuotientSystem B S hS C₀) (ψ : formalSpectrum E₀ ⟶ W)
        (_ : IsRepresentableEtale B S hS ψ)
        (G' : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR' s'))
          (Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' T) ⟶ formalSpectrum E₀),
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom ∧
          Space.completionSheafMap B S hS (yoneda.map f) T ≫ g = G' ≫ ψ := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let Y₁ := affineOver B S hS hR s
  obtain ⟨p, rfl⟩ := Quot.exists_rep q
  let s₀ : p.siteObject ⟶ Y₁ := p.value
  have hs₀T : Space.HasImageIn B S hS (yoneda.obj Y₁) T p.siteObject s₀ :=
    Space.hasImageIn_fieldValuedPoint p hq
  obtain ⟨Z₁, g₁, z₁, C₀, _, _, _, _, hCn, hCa, E₀, ψ, hψ, σ, hσ⟩ :=
    exists_pullback_section_of_isLocallyNoetherian B S hS hW g
      (presheafSection (F := yoneda.obj Y₁) B S hS s₀ hs₀T) (IsLocalRing.closedPoint p.carrier)
  have hfst := isRepresentableEtale_pullback_fst B S hS g ψ hψ
  obtain ⟨A, _, _, _, _, hCA, D, ⟨eD⟩⟩ := exists_formalSpectrum_iso_completionSheaf B S hS hR s T hT
  obtain ⟨K, C, _, fK, hfK, Q, gK, hgK, w, hw, hwrep, hwaff, hwnoeth, hsurj'⟩ :=
    exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCA D
      (pullback.fst g ψ ≫ eD.inv) (hfst.comp B S hS (isRepresentableEtale_of_isIso B S hS eD.inv))
  obtain ⟨Rs', hRs', hlift'⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff w).mp hsurj' σ
  obtain ⟨Z₂, g₂, -, hg₂, -, -, ⟨z₂, -⟩⟩ := BigFppfOver.exists_affine_mem_of_mem_topology B S hS
    hRs' z₁
  obtain ⟨k, t₂, ht₂⟩ := hlift' g₂ hg₂
  let a₂ : Z₂ ⟶ Y₁ := (yoneda.obj Y₁).map g₂.op ((yoneda.obj Y₁).map g₁.op s₀)
  have ha₁ : Space.HasImageIn B S hS (yoneda.obj Y₁) T Z₁ ((yoneda.obj Y₁).map g₁.op s₀) :=
    (Space.completionSubfunctor B S hS (yoneda.obj Y₁) T).map g₁.op (a := ULift.up s₀) hs₀T
  have ha₂ : Space.HasImageIn B S hS (yoneda.obj Y₁) T Z₂ a₂ :=
    (Space.completionSubfunctor B S hS (yoneda.obj Y₁) T).map g₂.op
      (a := ULift.up ((yoneda.obj Y₁).map g₁.op s₀)) ha₁
  obtain ⟨R', _, _, hR', s', _, f, hfE, v', hv', G', hG'r, hG'⟩ :=
    exists_etale_affineOver_lift_of_section B S hS hR s T hT g hg ψ hfst (w k) (hwrep k)
      (hwaff k) a₂ ha₂ t₂ (by
        rw [ht₂, NatTrans.naturality_apply (pullback.fst g ψ).hom g₂.op σ, hσ,
          presheafSection_map (F := yoneda.obj Y₁) (TF := T) B S hS g₁ s₀ hs₀T ha₁,
          presheafSection_map (F := yoneda.obj Y₁) (TF := T) B S hS g₂ _ ha₁ ha₂]) z₂
  refine ⟨R', inferInstance, inferInstance, hR', s', inferInstance, f, hfE, v', hv'.trans ?_, C₀,
    inferInstance, inferInstance, inferInstance, inferInstance, hCn, hCa, E₀, ψ, hψ, G', hG'r,
    hG'⟩
  change (BigFppfOver.toScheme B S hS).map (g₂ ≫ g₁ ≫ s₀) z₂ =
    (BigFppfOver.toScheme B S hS).map p.value (IsLocalRing.closedPoint p.carrier)
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  congr 1
  exact eq_closedPoint_of_isArtinianRing (.of p.carrier) _

end AlgebraicGeometry.FormalSpace
