module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSections05MF
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsLocalBase
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Module.Kaplansky

/-!
# Free sections near a flat point, for a morphism locally of finite type

Stacks Tag 05MF says: for `f : X ⟶ S` locally of finite *type*, `F` a quasi-coherent
`𝒪_X`-module of finite *type* and `x : X` a point at which `F` is flat over `S`, there are an
affine elementary étale neighbourhood `(S', s')` of `(S, f x)` and an affine open
`U' ⊆ X ×_S Spec 𝒪_{S', s'}` containing the point `x' = (x, s')` on which `Γ(U', F|_{U'})` is a
free `𝒪_{S', s'}`-module.

`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finitePresentation`
already has this for `f` locally of finite presentation and `F` of finite presentation. This
file removes both finite-presentation hypotheses, by the source's two reductions.

The first reduction removes the finite-presentation hypothesis on the *module*. Tag 05I5
(`AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver`) produces an
elementary étale neighbourhood `(S₁, s₁)` and an open `V ⊆ X ×_S Spec 𝒪_{S₁, s₁}` containing the
point over `x` on which the pullback of `F` *is* of finite presentation and flat over
`𝒪_{S₁, s₁}`; Tag 05ME (`AlgebraicGeometry.exists_affineOpen_projective_sections_of_chart`)
applies to `V ⟶ Spec 𝒪_{S₁, s₁}` and returns an affine elementary étale neighbourhood `E` of the
closed point of `Spec 𝒪_{S₁, s₁}` together with an affine open of `V ×_{Spec 𝒪_{S₁,s₁}} E` whose
sections are projective over `Γ(E, 𝒪_E)`. The two neighbourhoods are then composed into a single
elementary étale neighbourhood of `(S, f x)`: an étale algebra over the local ring `𝒪_{S₁, s₁}`
descends to an étale algebra over an affine open of `S₁`
(`StacksFrontier.RingTheory.Etale.FilteredColimit.Basic`'s `exists_isPushout_etale`), which realises
`E` as the base change of an affine étale neighbourhood `M` of `(S, f x)` along
`Spec 𝒪_{S₁, s₁} ⟶ S₁`; since that base change is flat and a preimmersion it is an isomorphism on
stalks, so `Spec 𝒪_{M, m}` lifts to `E`, and base changing the affine open along that lift turns
the projective sections into free ones by Kaplansky's theorem (Tag 0593).

The second reduction removes the finite-presentation hypothesis on the *morphism*. An affine
open `V ∋ x` embeds as a closed subscheme `i : V ⟶ A` of an affine space over an affine open of
`S` (`AlgebraicGeometry.exists_closedImmersion_affineSpace_of_locallyOfFiniteType`), with
`A ⟶ S` locally of finite presentation; the direct image `i_*(F|_V)` is quasi-coherent and of
finite type, and it is flat over `S` at `i x` because the fibre of `i` over `i x` is the single
point `x`. The first reduction applies to `A ⟶ S` and to that direct image, and the affine open
it returns in `A ×_S Spec 𝒪_{M, m}` is pulled back along the base change of `i` — a closed
immersion, so the preimage is again an affine open — and transported to `X ×_S Spec 𝒪_{M, m}`
along the base change of the open immersion `V ⟶ X`. Its sections do not change: pushforward
along the affine morphism `i` commutes with the base change (Tag 02KG) and the sections of a
pushforward over an open are the sections over its inverse image.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finiteType` is
  **Stacks Tag 05MF** for `f` locally of finite type and `F` of finite type, with no obligation.

## Implementation notes

The conclusion is the one of
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finitePresentation`
verbatim, so the two can be compared clause by clause.

The intermediate statement proved on the way, for `f` locally of finite presentation and `F` of
finite type only, additionally records that the image of `x'` in `Spec 𝒪_{S', s'}` is the closed
point, which is what the closed-immersion reduction needs in order to recover the clause on the
image of the point after transporting the open.

## References

* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 05ME](https://stacks.math.columbia.edu/tag/05ME)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/-- Every open of the source is contained in the preimage of the whole target, stated at the
exact type `Scheme.Hom.appLE` expects. Writing the inclusion as this application rather than as
`le_top` keeps the resulting `appLE` term type-correct at every transparency level, which is
what `rw` needs in order to see through it. -/
private lemma le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens) :
    V ≤ f ⁻¹ᵁ ⊤ :=
  le_top

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent,
stated for `Scheme.Modules` rather than for the underlying ringed spaces. The two types are
definitionally equal, but `Scheme.Modules` is semireducible, so the ringed-space instance is
not found for a `G : Y.Modules`; this wrapper passes it by hand. -/
private lemma isQuasicoherent_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
    [hG : G.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace
    Y.toRingedSpace f.toLRSHom.toShHom G hG

/-- Scalar extension preserves projectivity, using the presentation of the scalar extension as
the tensor product with the free rank-one module. -/
private lemma projective_scalarExtension
    {A R M : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M]
    [Module.Projective A M] : Module.Projective R (R ⊗[A] M) := by
  infer_instance

/-- After localizing the base at a point, the projective scalar extension supplied by 05ME is
free by Kaplansky's theorem. -/
private lemma free_scalarExtension_of_projective
    {A R M : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M]
    [Module.Projective A M] [IsLocalRing R] : Module.Free R (R ⊗[A] M) :=
  @Module.free_of_projective_of_isLocalRing R (R ⊗[A] M) _ _ _
    ‹IsLocalRing R› (projective_scalarExtension (A := A) (R := R) (M := M))

private lemma exists_etale_model_over_affineOpen
    (X : Scheme.{u}) (x : X) {T : CommRingCat.{u}}
    (f : X.presheaf.stalk x ⟶ T) (hf : f.hom.Etale) :
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (T₀ : CommRingCat.{u})
      (f₀ : Γ(X, U.1) ⟶ T₀) (g : T₀ ⟶ T),
      IsPushout (X.presheaf.germ U.1 x hx) f₀ f g ∧ f₀.hom.Etale := by
  let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
  obtain ⟨V, T₁, f₁, g₁, hsq, hf₁⟩ :=
    exists_isPushout_etale (colimit.isColimit D) f hf
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open V.unop.property V.unop.val.isOpen
  let ρ : Γ(X, V.unop.val) ⟶ Γ(X, U) :=
    X.presheaf.map (homOfLE hUV).op
  have hγ : ρ ≫ X.presheaf.germ U x hxU = colimit.ι D V :=
    X.presheaf.germ_res (homOfLE hUV) x hxU
  change IsPushout (colimit.ι D V) f₁ f g₁ at hsq
  rw [← hγ] at hsq
  have hp := IsPushout.of_left' hsq (IsPushout.of_hasPushout ρ f₁)
  exact ⟨⟨U, hU⟩, hxU, _, _, _, hp,
    CommRingCat.etale.pushout_inl ρ f₁ hf₁⟩

private lemma isPullback_postcompose_mono {C : Type*} [Category* C]
    {P X Y S T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback a b f g) (i : S ⟶ T) [Mono i] :
    IsPullback a b (f ≫ i) (g ≫ i) := by
  have h' : IsPullback g (𝟙 Y) i (g ≫ i) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert h'

private lemma exists_affine_etale_model_over_stalk
    (X : Scheme.{u}) (x : X) {T : CommRingCat.{u}}
    (f : X.presheaf.stalk x ⟶ T) (hf : f.hom.Etale) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (r : Spec T ⟶ Y),
      IsAffine Y ∧ Etale q ∧
        IsPullback (Spec.map f) r (X.fromSpecStalk x) q := by
  obtain ⟨U, hx, T₀, f₀, g, hsq, hf₀⟩ :=
    exists_etale_model_over_affineOpen X x f hf
  have : Etale (Spec.map f₀) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hf₀
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  refine ⟨Spec T₀, Spec.map f₀ ≫ U.2.fromSpec, Spec.map g, inferInstance,
    inferInstance, ?_⟩
  have h := isPullback_postcompose_mono
    (isPullback_SpecMap_of_isPushout _ _ _ _ hsq) U.2.fromSpec
  simpa only [← U.2.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk] using h

private lemma free_baseChange_of_projective
    {A B R C M : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra A C] [Algebra B C] [Algebra R C]
    [IsScalarTower A B C] [IsScalarTower A R C] [Algebra.IsPushout A R B C]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Projective A M] [IsLocalRing R] : Module.Free R (C ⊗[B] M) := by
  have : Module.Free R (R ⊗[A] M) := free_scalarExtension_of_projective
  exact Module.Free.of_equiv (Algebra.IsPushout.cancelBaseChange A R B C M).symm

private lemma exists_affine_etale_model
    (X : Scheme.{u}) (x : X) {E : Scheme.{u}} [IsAffine E]
    (p : E ⟶ Spec (X.presheaf.stalk x)) [Etale p] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (r : E ⟶ Y),
      IsAffine Y ∧ Etale q ∧ IsPullback p r (X.fromSpecStalk x) q ∧
      ∀ e : E, IsIso (r.stalkMap e) := by
  let φ : X.presheaf.stalk x ⟶ Γ(E, ⊤) :=
    (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫ p.appTop
  have heq : Spec.map φ = E.isoSpec.inv ≫ p := by
    dsimp [φ]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have : Etale (Spec.map φ) := heq.symm ▸ inferInstance
  obtain ⟨Y, q, r₀, hY, hq, hp⟩ := exists_affine_etale_model_over_stalk X x φ
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance)
  let r := E.isoSpec.hom ≫ r₀
  have hp' : IsPullback p r (X.fromSpecStalk x) q :=
    hp.of_iso E.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using heq) (by simp [r]) (by simp) (by simp)
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : Flat r := MorphismProperty.of_isPullback hp' inferInstance
  have : IsPreimmersion r := MorphismProperty.of_isPullback hp' inferInstance
  exact ⟨Y, q, r, hY, hq, hp', isIso_stalkMap_of_flat_isPreimmersion r⟩

private lemma exists_affine_elementaryEtale_model
    (X : Scheme.{u}) (x : X)
    (E : AlgebraicGeometry.EtaleNeighborhood (Spec (X.presheaf.stalk x))
      (IsLocalRing.closedPoint (X.presheaf.stalk x)))
    (hE : E.IsElementary) [IsAffine E.scheme] :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood X x) (r : E.scheme ⟶ N.scheme),
      N.IsElementary ∧ IsAffine N.scheme ∧ r E.point = N.point ∧
      IsPullback E.toBase r (X.fromSpecStalk x) N.toBase ∧
      IsIso (r.stalkMap E.point) := by
  let := E.etale_toBase
  obtain ⟨Y, q, r, hY, hq, hp, hr⟩ := exists_affine_etale_model X x E.toBase
  have hpoint : q (r E.point) = x := by
    rw [← Scheme.Hom.comp_apply, ← hp.w, Scheme.Hom.comp_apply, E.map_point,
      Scheme.fromSpecStalk_closedPoint]
  let : Etale q := hq
  let : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : IsIso (E.toBase.residueFieldMap E.point) := E.isElementary_iff.mp hE
  have : IsIso ((X.fromSpecStalk x).stalkMap (E.toBase E.point)) :=
    isIso_stalkMap_of_flat_isPreimmersion _ _
  have : IsIso ((X.fromSpecStalk x).residueFieldMap (E.toBase E.point)) :=
    isIso_residueFieldMap_of_isIso_stalkMap _ _
  have hrq : IsIso ((r ≫ q).residueFieldMap E.point) := by
    have hc : IsIso ((E.toBase ≫ X.fromSpecStalk x).residueFieldMap E.point) := by
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso'
        (inferInstance : IsIso ((X.fromSpecStalk x).residueFieldMap (E.toBase E.point)))
        (inferInstance : IsIso (E.toBase.residueFieldMap E.point))
    rwa [hp.w] at hc
  have : IsIso (r.stalkMap E.point) := hr E.point
  have : IsIso (r.residueFieldMap E.point) :=
    isIso_residueFieldMap_of_isIso_stalkMap _ _
  have : IsIso (q.residueFieldMap (r E.point) ≫ r.residueFieldMap E.point) := by
    rwa [← Scheme.residueFieldMap_comp]
  have : IsIso (q.residueFieldMap (r E.point)) :=
    IsIso.of_isIso_comp_right _ (r.residueFieldMap E.point)
  let N : AlgebraicGeometry.EtaleNeighborhood X x := ⟨Y, r E.point, q, hpoint⟩
  exact ⟨N, r, N.isElementary_iff.mpr inferInstance, hY, rfl, hp, hr E.point⟩

private lemma free_sections_of_isPullback
    {X S P : Scheme.{u}} [IsAffine X] [IsAffine S]
    (R : CommRingCat.{u}) [IsLocalRing R]
    (a : P ⟶ X) (b : P ⟶ Spec R) (q : X ⟶ S) (g : Spec R ⟶ S)
    (hp : IsPullback a b q g) (F : X.Modules) [F.IsQuasicoherent]
    (hproj : letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ q.appTop.hom
      Module.Projective Γ(S, ⊤) Γ(F, ⊤)) :
    letI : Module R Γ((Scheme.Modules.pullback a).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ b.appTop).hom
    Module.Free R Γ((Scheme.Modules.pullback a).obj F, ⊤) := by
  have : IsAffine P := IsAffine.of_isPullback hp
  let α : Γ(S, ⊤) ⟶ R := g.appTop ≫ (Scheme.ΓSpecIso R).hom
  let β : R ⟶ Γ(P, ⊤) := (Scheme.ΓSpecIso R).inv ≫ b.appTop
  have hs : IsPushout α q.appTop β a.appTop := by
    apply (isPushout_appTop_of_isPullback hp).flip.of_iso (Iso.refl _)
      (Scheme.ΓSpecIso R) (Iso.refl _) (Iso.refl _)
    all_goals first
      | exact Category.comp_id _
      | simp [α, β]
  let : Algebra Γ(S, ⊤) R := α.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  let : Algebra R Γ(P, ⊤) := β.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(P, ⊤) := a.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(P, ⊤) := (α ≫ β).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) R Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hs.w)
  have : Algebra.IsPushout Γ(S, ⊤) R Γ(X, ⊤) Γ(P, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hs
  let : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ q.appTop.hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
    IsScalarTower.of_compHom _ _ _
  have : Module.Projective Γ(S, ⊤) Γ(F, ⊤) := hproj
  let : Module R Γ((Scheme.Modules.pullback a).obj F, ⊤) := Module.compHom _ β.hom
  have : IsScalarTower R Γ(P, ⊤) Γ((Scheme.Modules.pullback a).obj F, ⊤) :=
    IsScalarTower.of_compHom _ _ _
  have : Module.Free R (Γ(P, ⊤) ⊗[Γ(X, ⊤)] Γ(F, ⊤)) :=
    free_baseChange_of_projective (A := Γ(S, ⊤))
  let e : (Γ(P, ⊤) ⊗[Γ(X, ⊤)] Γ(F, ⊤)) ≃ₗ[Γ(P, ⊤)]
      Γ((Scheme.Modules.pullback a).obj F, ⊤) :=
    by
      have happ : a.appLE ⊤ ⊤ (le_preimage_top a ⊤) = a.appTop := Scheme.Hom.appLE_eq_app a
      have e₀ := affinePullbackSectionsBaseChangeIso a F (U := ⊤) (isAffineOpen_top X)
        (V := ⊤) (isAffineOpen_top P) (by simp)
      rw [happ] at e₀
      exact e₀.toLinearEquiv
  exact Module.Free.of_equiv (e.restrictScalars R)

private noncomputable def openPullbackSectionsLinearEquiv
    {X D : Scheme.{u}} (j : D ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (R : CommRingCat.{u}) (U : D.Opens) (α : R ⟶ Γ(X, j ''ᵁ U)) :
    letI : Module R Γ((Scheme.Modules.pullback j).obj F, U) :=
      Module.compHom _ (α ≫ (j.appIso U).hom).hom
    letI : Module R Γ(F, j ''ᵁ U) := Module.compHom _ α.hom
    Γ((Scheme.Modules.pullback j).obj F, U) ≃ₗ[R] Γ(F, j ''ᵁ U) := by
  letI : Module R Γ((Scheme.Modules.pullback j).obj F, U) :=
    Module.compHom _ (α ≫ (j.appIso U).hom).hom
  letI : Module R Γ(F, j ''ᵁ U) := Module.compHom _ α.hom
  let e₁ : Γ((Scheme.Modules.pullback j).obj F, U) ≃ₗ[Γ(D, U)]
      Γ(F.restrict j, U) :=
    ((SheafOfModules.evaluation _ (.op U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm).toLinearEquiv
  let e₂ := Scheme.Modules.restrictAppIso j F U
  let e : Γ((Scheme.Modules.pullback j).obj F, U) ≃ Γ(F, j ''ᵁ U) :=
    e₁.toEquiv.trans (Equiv.ofBijective (ConcreteCategory.hom e₂.hom)
      (ConcreteCategory.bijective_of_isIso _))
  refine LinearEquiv.ofBijective
    { toFun := e
      map_add' := ?_
      map_smul' := ?_ } e.bijective
  · intro a b
    exact (congrArg (fun z => (ConcreteCategory.hom e₂.hom) z)
      (e₁.map_add a b)).trans (map_add (ConcreteCategory.hom e₂.hom) _ _)
  · intro r m
    change (ConcreteCategory.hom e₂.hom) (e₁ (((α ≫ (j.appIso U).hom) r) • m)) =
      (α r) • (ConcreteCategory.hom e₂.hom) (e₁ m)
    rw [e₁.map_smul]
    dsimp only [e₂]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp

/-- Freeness of the sections over `U` of a module over `R` transfers along an isomorphism of
modules, the scalars acting through a ring map `β : R ⟶ Γ(Z, U)`. -/
private lemma free_sections_of_iso {Z : Scheme.{u}} {G H : Z.Modules} (e : G ≅ H)
    (U : Z.Opens) {R : CommRingCat.{u}} (β : R ⟶ Γ(Z, U))
    (hfree : letI : Module R Γ(G, U) := Module.compHom _ β.hom
      Module.Free R Γ(G, U)) :
    letI : Module R Γ(H, U) := Module.compHom _ β.hom
    Module.Free R Γ(H, U) := by
  let : Algebra R Γ(Z, U) := β.hom.toAlgebra
  let : Module R Γ(G, U) := Module.compHom _ β.hom
  let : Module R Γ(H, U) := Module.compHom _ β.hom
  have : IsScalarTower R Γ(Z, U) Γ(G, U) := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower R Γ(Z, U) Γ(H, U) := IsScalarTower.of_compHom _ _ _
  have : Module.Free R Γ(G, U) := hfree
  let eΓ : Γ(G, U) ≃ₗ[Γ(Z, U)] Γ(H, U) :=
    ((SheafOfModules.evaluation _ (.op U)).mapIso e).toLinearEquiv
  exact Module.Free.of_equiv (eΓ.restrictScalars R)

private lemma free_sections_image_of_isOpenImmersion_at_open
    {X D : Scheme.{u}} (j : D ⟶ X) [IsOpenImmersion j]
    (R : CommRingCat.{u}) (q : X ⟶ Spec R) (F : X.Modules)
    (U : D.Opens)
    (hfree : letI : Module R Γ((Scheme.Modules.pullback j).obj F, U) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
        (j ≫ q).appLE ⊤ U (le_preimage_top _ _)).hom
      Module.Free R Γ((Scheme.Modules.pullback j).obj F, U)) :
    letI : Module R Γ(F, j ''ᵁ U) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
        q.appLE ⊤ (j ''ᵁ U) (le_preimage_top _ _)).hom
    Module.Free R Γ(F, j ''ᵁ U) := by
  let α := (Scheme.ΓSpecIso R).inv ≫ q.appLE ⊤ (j ''ᵁ U) (le_preimage_top _ _)
  have hβ : α ≫ (j.appIso U).hom =
      (Scheme.ΓSpecIso R).inv ≫ (j ≫ q).appLE ⊤ U (le_preimage_top _ _) := by
    dsimp only [α]
    rw [Category.assoc, Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  let : Module R Γ((Scheme.Modules.pullback j).obj F, U) :=
    Module.compHom _ (α ≫ (j.appIso U).hom).hom
  have : Module.Free R Γ((Scheme.Modules.pullback j).obj F, U) := by
    change @Module.Free R _ _ _ (Module.compHom _ (α ≫ (j.appIso U).hom).hom)
    rw [hβ]
    exact hfree
  let : Module R Γ(F, j ''ᵁ U) := Module.compHom _ α.hom
  exact Module.Free.of_equiv (openPullbackSectionsLinearEquiv j F R U α)

private lemma free_sections_image_of_isOpenImmersion
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : CommRingCat.{u}) (q : X ⟶ Spec R) (F : X.Modules)
    (hfree : letI : Module R Γ((Scheme.Modules.pullback j).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (j ≫ q).appTop).hom
      Module.Free R Γ((Scheme.Modules.pullback j).obj F, ⊤)) :
    letI : Module R Γ(F, j ''ᵁ (⊤ : U.Opens)) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
        q.appLE ⊤ (j ''ᵁ (⊤ : U.Opens)) (le_preimage_top _ _)).hom
    Module.Free R Γ(F, j ''ᵁ (⊤ : U.Opens)) :=
  free_sections_image_of_isOpenImmersion_at_open j R q F ⊤
    (by
      rw [show (j ≫ q).appLE ⊤ ⊤ (le_preimage_top _ _) = (j ≫ q).appTop from
        Scheme.Hom.appLE_eq_app _]
      exact hfree)

private noncomputable def openPullbackSectionsOverLinearEquiv
    {X U S : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (q : X ⟶ S) (F : X.Modules) :
    letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback j).obj F, ⊤) :=
      Module.compHom _ (j ≫ q).appTop.hom
    letI : Module Γ(S, ⊤) Γ(F, j ''ᵁ (⊤ : U.Opens)) :=
      Module.compHom _ (q.appLE ⊤ (j ''ᵁ (⊤ : U.Opens)) (le_preimage_top _ _)).hom
    Γ((Scheme.Modules.pullback j).obj F, ⊤) ≃ₗ[Γ(S, ⊤)]
      Γ(F, j ''ᵁ (⊤ : U.Opens)) := by
  have hβ : q.appLE ⊤ (j ''ᵁ (⊤ : U.Opens)) (le_preimage_top _ _) ≫ (j.appIso ⊤).hom =
      (j ≫ q).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_eq_app _
  have e := openPullbackSectionsLinearEquiv j F Γ(S, ⊤) ⊤
    (q.appLE ⊤ (j ''ᵁ (⊤ : U.Opens)) (le_preimage_top _ _))
  rw [hβ] at e
  exact e

private noncomputable def opensPullbackSectionsOverLinearEquiv
    {X S : Scheme.{u}} (q : X ⟶ S) (F : X.Modules) (U : X.Opens) :
    letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback U.ι).obj F, ⊤) :=
      Module.compHom _ (U.ι ≫ q).appTop.hom
    letI : Module Γ(S, ⊤) Γ(F, U) :=
      Module.compHom _ (q.appLE ⊤ U (le_preimage_top _ _)).hom
    Γ((Scheme.Modules.pullback U.ι).obj F, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(F, U) := by
  have e := openPullbackSectionsOverLinearEquiv U.ι q F
  rw [Scheme.Opens.ι_image_top] at e
  exact e

private lemma free_sections_preimage_of_projective
    {X S P : Scheme.{u}} [IsAffine S]
    (R : CommRingCat.{u}) [IsLocalRing R]
    (a : P ⟶ X) (b : P ⟶ Spec R) (q : X ⟶ S) (g : Spec R ⟶ S)
    (hp : IsPullback a b q g) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (hproj : letI : Module Γ(S, ⊤) Γ(F, U) :=
      Module.compHom _ (q.appLE ⊤ U (le_preimage_top _ _)).hom
      Module.Projective Γ(S, ⊤) Γ(F, U)) :
    IsAffineOpen (a ⁻¹ᵁ U) ∧
      letI : Module R Γ((Scheme.Modules.pullback a).obj F, a ⁻¹ᵁ U) :=
        Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
          b.appLE ⊤ (a ⁻¹ᵁ U) (le_preimage_top _ _)).hom
      Module.Free R Γ((Scheme.Modules.pullback a).obj F, a ⁻¹ᵁ U) := by
  let W := a ⁻¹ᵁ U
  let FU := (Scheme.Modules.pullback U.ι).obj F
  let FW := (Scheme.Modules.pullback a).obj F
  have : IsAffine U.toScheme := hU
  have hs : IsPullback (a ∣_ U) (W.ι ≫ b) (U.ι ≫ q) g :=
    (isPullback_morphismRestrict a U).paste_vert hp
  have hW : IsAffineOpen W := IsAffine.of_isPullback hs
  refine ⟨hW, ?_⟩
  have hpU : let : Module Γ(S, ⊤) Γ(FU, ⊤) :=
      Module.compHom _ (U.ι ≫ q).appTop.hom
      Module.Projective Γ(S, ⊤) Γ(FU, ⊤) := by
    let : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (q.appLE ⊤ U (le_preimage_top _ _)).hom
    let : Module Γ(S, ⊤) Γ(FU, ⊤) := Module.compHom _ (U.ι ≫ q).appTop.hom
    have : Module.Projective Γ(S, ⊤) Γ(F, U) := hproj
    exact Module.Projective.of_equiv (opensPullbackSectionsOverLinearEquiv q F U).symm
  have : FU.IsQuasicoherent := isQuasicoherent_pullback U.ι F
  have hf := free_sections_of_isPullback R (a ∣_ U) (W.ι ≫ b) (U.ι ≫ q) g hs FU hpU
  let F₁ := (Scheme.Modules.pullback (a ∣_ U)).obj FU
  let F₂ := (Scheme.Modules.pullback W.ι).obj FW
  let e : F₁ ≅ F₂ :=
    (Scheme.Modules.pullbackComp (a ∣_ U) U.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι a U)).app F ≪≫
        ((Scheme.Modules.pullbackComp W.ι a).app F).symm
  have hfW := free_sections_image_of_isOpenImmersion W.ι R b FW
    (free_sections_of_iso e ⊤ _ hf)
  rw [Scheme.Opens.ι_image_top] at hfW
  exact hfW

private lemma exists_affine_elementaryEtale_model_over_base
    {S : Scheme.{u}} {s : S} (N : AlgebraicGeometry.EtaleNeighborhood S s)
    (hN : N.IsElementary)
    (E : AlgebraicGeometry.EtaleNeighborhood (Spec (N.scheme.presheaf.stalk N.point))
      (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)))
    (hE : E.IsElementary) [IsAffine E.scheme] :
    ∃ (M : AlgebraicGeometry.EtaleNeighborhood S s) (r : E.scheme ⟶ M.scheme),
      M.IsElementary ∧ IsAffine M.scheme ∧ r E.point = M.point ∧
      E.toBase ≫ N.scheme.fromSpecStalk N.point ≫ N.toBase = r ≫ M.toBase ∧
      IsIso (r.stalkMap E.point) := by
  obtain ⟨M₀, r, hM₀, hA, hr, hs, hi⟩ :=
    exists_affine_elementaryEtale_model N.scheme N.point E hE
  let := N.etale_toBase
  let := M₀.etale_toBase
  let M : AlgebraicGeometry.EtaleNeighborhood S s := {
    scheme := M₀.scheme
    point := M₀.point
    toBase := M₀.toBase ≫ N.toBase
    etale_toBase := inferInstance
    map_point := by simp only [Scheme.Hom.comp_apply, M₀.map_point, N.map_point] }
  have : IsIso (N.toBase.residueFieldMap N.point) := N.isElementary_iff.mp hN
  have hM₀b : IsIso (M₀.toBase.residueFieldMap M₀.point) := M₀.isElementary_iff.mp hM₀
  have hNb : IsIso (N.toBase.residueFieldMap (M₀.toBase M₀.point)) := by
    rw [M₀.map_point]
    infer_instance
  have hMb : IsIso (M.toBase.residueFieldMap M.point) := by
    dsimp only [M]
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hNb hM₀b
  exact ⟨M, r, M.isElementary_iff.mpr hMb, hA, hr, hs.w_assoc N.toBase, hi⟩

private lemma exists_projective_sections_over_local_base
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood S (f x)) (_ : N.IsElementary),
      let b := N.scheme.fromSpecStalk N.point ≫ N.toBase
      let P : Scheme.{u} := pullback f b
      ∃ (V : P.Opens) (v : V),
        pullback.fst f b (V.ι v) = x ∧
        pullback.snd f b (V.ι v) = IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point) ∧
        let q : V.toScheme ⟶ Spec (N.scheme.presheaf.stalk N.point) := V.ι ≫ pullback.snd f b
        let FV := (Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F
        ∃ (E : AlgebraicGeometry.EtaleNeighborhood (Spec (N.scheme.presheaf.stalk N.point))
          (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)))
          (_ : E.IsElementary) (_ : IsAffine E.scheme)
          (y : pullback (C := Scheme.{u}) q E.toBase) (U : (pullback q E.toBase).Opens),
          pullback.fst q E.toBase y = v ∧ pullback.snd q E.toBase y = E.point ∧
          IsAffineOpen U ∧ y ∈ U ∧
          let G := (Scheme.Modules.pullback (pullback.fst q E.toBase)).obj FV
          letI : Module Γ(E.scheme, ⊤) Γ(G, U) :=
            Module.compHom _ ((pullback.snd q E.toBase).appLE ⊤ U (le_preimage_top _ _)).hom
          Module.Projective Γ(E.scheme, ⊤) Γ(G, U) := by
  obtain ⟨N, hN, V, v, hv, hfp, hfl⟩ :=
    existsElementaryEtaleNeighborhoodFinitePresentationFlatOver f F x hflat
  let b := N.scheme.fromSpecStalk N.point ≫ N.toBase
  have hvX : pullback.fst f b (V.ι v) = x :=
    show V.ι v ∈ pullback.fst f b ⁻¹' {x} by rw [hv]; exact Set.mem_singleton _
  have hbase : b (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)) = f x :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun z : N.scheme => N.toBase z)
        (Scheme.fromSpecStalk_closedPoint (x := N.point))).trans N.map_point)
  obtain ⟨z, hzX, hzN⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := b) x
    (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)) hbase.symm
  have hz : z = V.ι v := by
    have h : z ∈ pullback.fst f b ⁻¹' {x} := hzX
    rwa [hv, Set.mem_singleton_iff] at h
  have hvN : pullback.snd f b (V.ι v) =
      IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point) := hz ▸ hzN
  let q : V.toScheme ⟶ Spec (N.scheme.presheaf.stalk N.point) := V.ι ≫ pullback.snd f b
  let FV := (Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F
  let : FV.IsFinitePresentation := hfp
  let : FV.IsQuasicoherent := isQuasicoherent_pullback (V.ι ≫ pullback.fst f b) F
  have : LocallyOfFinitePresentation q := by dsimp [q]; infer_instance
  obtain ⟨E₀, hE₀, hEA, y, hyV, hyE, U, hU, hyU, hproj⟩ :=
    exists_affineOpen_projective_sections_of_chart q FV (q v) v rfl (hfl v)
  let := E₀.etale_toBase
  let E : AlgebraicGeometry.EtaleNeighborhood (Spec (N.scheme.presheaf.stalk N.point))
      (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)) := {
    scheme := E₀.scheme
    point := E₀.point
    toBase := E₀.toBase
    map_point := E₀.map_point.trans hvN }
  have hE : E.IsElementary := E.isElementary_iff.mpr (E₀.isElementary_iff.mp hE₀)
  exact ⟨N, hN, V, v, hvX, hvN, E, hE, hEA, y, U, hyV, hyE, hU, hyU, hproj⟩

private lemma exists_lift_localScheme_of_isIso_stalkMap
    {X Y : Scheme.{u}} (r : X ⟶ Y) (x : X) (y : Y) (h : r x = y)
    [IsIso (r.stalkMap x)] :
    ∃ t : Spec (Y.presheaf.stalk y) ⟶ X,
      t ≫ r = Y.fromSpecStalk y ∧
      t (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = x := by
  subst y
  let e : Y.presheaf.stalk (r x) ≅ X.presheaf.stalk x := asIso (r.stalkMap x)
  let t := Spec.map e.inv ≫ X.fromSpecStalk x
  refine ⟨t, ?_, ?_⟩
  · dsimp only [t]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk r,
      ← Spec.map_comp_assoc]
    change Spec.map (e.hom ≫ e.inv) ≫ Y.fromSpecStalk (r x) = _
    simp
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun z : Spec (X.presheaf.stalk x) => (X.fromSpecStalk x) z)
        (Spec_closedPoint (f := e.inv))).trans
        (Scheme.fromSpecStalk_closedPoint (x := x)))

private lemma exists_affine_elementaryEtale_local_lift
    {S : Scheme.{u}} {s : S} (N : AlgebraicGeometry.EtaleNeighborhood S s)
    (hN : N.IsElementary)
    (E : AlgebraicGeometry.EtaleNeighborhood (Spec (N.scheme.presheaf.stalk N.point))
      (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point)))
    (hE : E.IsElementary) [IsAffine E.scheme] :
    ∃ (M : AlgebraicGeometry.EtaleNeighborhood S s)
      (t : Spec (M.scheme.presheaf.stalk M.point) ⟶ E.scheme),
      M.IsElementary ∧ IsAffine M.scheme ∧
      t (IsLocalRing.closedPoint (M.scheme.presheaf.stalk M.point)) = E.point ∧
      t ≫ E.toBase ≫ N.scheme.fromSpecStalk N.point ≫ N.toBase =
        M.scheme.fromSpecStalk M.point ≫ M.toBase := by
  obtain ⟨M, r, hM, hMA, hr, hc, hi⟩ :=
    exists_affine_elementaryEtale_model_over_base N hN E hE
  have : IsIso (r.stalkMap E.point) := hi
  obtain ⟨t, ht, htx⟩ := exists_lift_localScheme_of_isIso_stalkMap r E.point M.point hr
  refine ⟨M, t, hM, hMA, htx, ?_⟩
  rw [hc, ← Category.assoc, ht]

/-- Given `t ≫ e ≫ b = g`, an open `V` of `X ×_S B` pulls back to an open `D` of `X ×_S Q`
which is the base change of `V ×_B E` along `t`, compatibly with the projections to `X`. -/
private lemma exists_isPullback_of_comp_eq
    {X S B Q E : Scheme.{u}} (f : X ⟶ S) (b : B ⟶ S) (g : Q ⟶ S)
    (V : (pullback f b).Opens) (e : E ⟶ B) (t : Q ⟶ E) (ht : t ≫ e ≫ b = g) :
    ∃ (D : (pullback f g).Opens) (d : D.toScheme ⟶ pullback (V.ι ≫ pullback.snd f b) e),
      IsPullback d (D.ι ≫ pullback.snd f g) (pullback.snd (V.ι ≫ pullback.snd f b) e) t ∧
        d ≫ pullback.fst (V.ι ≫ pullback.snd f b) e ≫ V.ι ≫ pullback.fst f b =
          D.ι ≫ pullback.fst f g := by
  let q : V.toScheme ⟶ B := V.ι ≫ pullback.snd f b
  let c : Q ⟶ B := t ≫ e
  have hgc : c ≫ b = g := by simpa only [c, Category.assoc] using ht
  let a : pullback f g ⟶ pullback f b := pullback.lift (pullback.fst f g)
    (pullback.snd f g ≫ c) (by rw [Category.assoc, hgc, pullback.condition])
  have haX : a ≫ pullback.fst f b = pullback.fst f g := pullback.lift_fst _ _ _
  have haB : a ≫ pullback.snd f b = pullback.snd f g ≫ c := pullback.lift_snd _ _ _
  have haPB : IsPullback a (pullback.snd f g) (pullback.snd f b) c := by
    have h : IsPullback (a ≫ pullback.fst f b) (pullback.snd f g) f (c ≫ b) := by
      rw [hgc, haX]
      exact IsPullback.of_hasPullback f g
    exact h.of_right haB (IsPullback.of_hasPullback f b)
  let D := a ⁻¹ᵁ V
  let j : D.toScheme ⟶ pullback f g := D.ι
  have hjPB : IsPullback (a ∣_ V) (j ≫ pullback.snd f g) q c :=
    (isPullback_morphismRestrict a V).paste_vert haPB
  let d : D.toScheme ⟶ pullback q e := pullback.lift (a ∣_ V)
    (j ≫ pullback.snd f g ≫ t) (by
      dsimp only [q]
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, haB]
      simp [c, j]
      rfl)
  have hdV : d ≫ pullback.fst q e = a ∣_ V := pullback.lift_fst _ _ _
  have hdE : d ≫ pullback.snd q e = j ≫ pullback.snd f g ≫ t := pullback.lift_snd _ _ _
  have hdPB : IsPullback d (j ≫ pullback.snd f g) (pullback.snd q e) t := by
    have h : IsPullback (d ≫ pullback.fst q e) (j ≫ pullback.snd f g) q c := by
      rwa [hdV]
    exact h.of_right hdE (IsPullback.of_hasPullback q e)
  refine ⟨D, d, hdPB, ?_⟩
  change d ≫ pullback.fst q e ≫ V.ι ≫ pullback.fst f b = _
  calc
    _ = ((d ≫ pullback.fst q e) ≫ V.ι) ≫ pullback.fst f b := by
      simp only [Category.assoc]
    _ = ((a ∣_ V) ≫ V.ι) ≫ pullback.fst f b := by rw [hdV]
    _ = (j ≫ a) ≫ pullback.fst f b := by rw [morphismRestrict_ι]
    _ = j ≫ pullback.fst f g := by rw [Category.assoc, haX]

/-- Freeness of sections over `U` of a module isomorphic to the pullback of `H` along an open
immersion `k` gives freeness of the sections of `H` over the image `k ''ᵁ U`. -/
private lemma free_sections_image_of_isOpenImmersion_of_iso
    {Z T : Scheme.{u}} (k : Z ⟶ T) [IsOpenImmersion k] (R : CommRingCat.{u})
    (q : T ⟶ Spec R) (c : Z ⟶ Spec R) (hc : k ≫ q = c) (H : T.Modules) (G : Z.Modules)
    (e : G ≅ (Scheme.Modules.pullback k).obj H) (U : Z.Opens)
    (hfree : letI : Module R Γ(G, U) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ c.appLE ⊤ U (le_preimage_top _ _)).hom
      Module.Free R Γ(G, U)) :
    letI : Module R Γ(H, k ''ᵁ U) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
        q.appLE ⊤ (k ''ᵁ U) (le_preimage_top _ _)).hom
    Module.Free R Γ(H, k ''ᵁ U) := by
  subst hc
  exact free_sections_image_of_isOpenImmersion_at_open k R q H U (free_sections_of_iso e U _ hfree)

private lemma exists_free_sections_of_locallyFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (M : AlgebraicGeometry.EtaleNeighborhood S (f x)),
      M.IsElementary ∧ IsAffine M.scheme ∧
        let g := M.scheme.fromSpecStalk M.point ≫ M.toBase
        let T := pullback f g
        ∃ (z : T) (W : T.Opens),
          pullback.fst f g z = x ∧
            M.scheme.fromSpecStalk M.point (pullback.snd f g z) = M.point ∧
            pullback.snd f g z =
              IsLocalRing.closedPoint (M.scheme.presheaf.stalk M.point) ∧
            IsAffineOpen W ∧ z ∈ W ∧
              let H := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (M.scheme.presheaf.stalk M.point) Γ(H, W) :=
                Module.compHom Γ(H, W)
                  (((Scheme.ΓSpecIso (.of (M.scheme.presheaf.stalk M.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (le_preimage_top _ _)).hom)
              Module.Free (M.scheme.presheaf.stalk M.point) Γ(H, W) := by
  classical
  obtain ⟨N, hN, V, v, hvX, hvB, E, hE, hEA, y, U, hyV, hyE, hU, hyU, hproj⟩ :=
    exists_projective_sections_over_local_base f F x hflat
  let : IsAffine E.scheme := hEA
  obtain ⟨M, t, hM, hMA, htpoint, ht⟩ :=
    exists_affine_elementaryEtale_local_lift N hN E hE
  let B := Spec (N.scheme.presheaf.stalk N.point)
  let L := M.scheme.presheaf.stalk M.point
  let b : B ⟶ S := N.scheme.fromSpecStalk N.point ≫ N.toBase
  let g : Spec L ⟶ S := M.scheme.fromSpecStalk M.point ≫ M.toBase
  let T := pullback f g
  let q : V.toScheme ⟶ B := V.ι ≫ pullback.snd f b
  let Z := pullback q E.toBase
  obtain ⟨D, d, hdPB, hpath⟩ : ∃ (D : T.Opens) (d : D.toScheme ⟶ Z),
      IsPullback d (D.ι ≫ pullback.snd f g) (pullback.snd q E.toBase) t ∧
        d ≫ pullback.fst q E.toBase ≫ V.ι ≫ pullback.fst f b = D.ι ≫ pullback.fst f g :=
    exists_isPullback_of_comp_eq f b g V E.toBase t ht
  let j : D.toScheme ⟶ T := D.ι
  let FV := (Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F
  let HZ := (Scheme.Modules.pullback (pullback.fst q E.toBase)).obj FV
  have : HZ.IsQuasicoherent := by
    have : FV.IsQuasicoherent := isQuasicoherent_pullback (V.ι ≫ pullback.fst f b) F
    exact isQuasicoherent_pullback (pullback.fst q E.toBase) FV
  have hproj' : let : Module Γ(E.scheme, ⊤) Γ(HZ, U) :=
      Module.compHom _ ((pullback.snd q E.toBase).appLE ⊤ U (le_preimage_top _ _)).hom
      Module.Projective Γ(E.scheme, ⊤) Γ(HZ, U) := hproj
  obtain ⟨hWU, hfree⟩ :=
    free_sections_preimage_of_projective (.of L) d (j ≫ pullback.snd f g)
      (pullback.snd q E.toBase) t hdPB HZ U hU hproj'
  obtain ⟨z₀, hzZ, hzL⟩ := Scheme.exists_preimage_of_isPullback hdPB y
    (IsLocalRing.closedPoint L) (by rw [hyE, htpoint])
  let W₀ := d ⁻¹ᵁ U
  have hzW : j z₀ ∈ j ''ᵁ W₀ := ⟨z₀, by change d z₀ ∈ U; rwa [hzZ], rfl⟩
  refine ⟨M, hM, hMA, j z₀, j ''ᵁ W₀, ?_, ?_, hzL, hWU.image_of_isOpenImmersion j, hzW, ?_⟩
  · have h := congrArg (fun k : D.toScheme ⟶ X => k z₀) hpath
    simp only [Scheme.Hom.comp_apply] at h
    rw [hzZ, hyV, hvX] at h
    exact h.symm
  · change M.scheme.fromSpecStalk M.point ((j ≫ pullback.snd f g) z₀) = M.point
    rw [hzL, Scheme.fromSpecStalk_closedPoint]
  · let H := (Scheme.Modules.pullback (pullback.fst f g)).obj F
    let e : (Scheme.Modules.pullback d).obj HZ ≅ (Scheme.Modules.pullback j).obj H :=
      (Scheme.Modules.pullbackComp d (pullback.fst q E.toBase)).app FV ≪≫
        (Scheme.Modules.pullbackComp
          (d ≫ pullback.fst q E.toBase)
          (V.ι ≫ pullback.fst f b)).app F ≪≫
        (Scheme.Modules.pullbackCongr hpath).app F ≪≫
        ((Scheme.Modules.pullbackComp j (pullback.fst f g)).app F).symm
    exact free_sections_image_of_isOpenImmersion_of_iso j (.of L) (pullback.snd f g) _ rfl H _
      e W₀ hfree

private lemma isFlatOverAt_pushforward_of_finite_singleton_fiber
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsFinite i] (g : Y ⟶ S)
    (x : X) (hi : i ⁻¹' {i x} = {x}) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : AlgebraicGeometry.IsFlatOverAt (i ≫ g).toLRSHom.toShHom F x) :
    AlgebraicGeometry.IsFlatOverAt g.toLRSHom.toShHom
      ((Scheme.Modules.pushforward i).obj F) (i x) := by
  let M := TopCat.Presheaf.stalk F.val.presheaf x
  let G := (Scheme.Modules.pushforward i).obj F
  let Q := TopCat.Presheaf.stalk G.val.presheaf (i x)
  let A := S.presheaf.stalk (g (i x))
  let B := Y.presheaf.stalk (i x)
  let : Algebra A B := (g.stalkMap (i x)).hom.toAlgebra
  let : Module (X.presheaf.stalk x) M := inferInstance
  let : Module B M := Module.compHom _ (i.stalkMap x).hom
  let : Module A M := Module.compHom _ (g.stalkMap (i x)).hom
  let : Module A Q := Module.compHom _ (g.stalkMap (i x)).hom
  have : IsScalarTower A B M := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower A B Q := IsScalarTower.of_compHom _ _ _
  have : Module.Flat A M := by
    change @Module.Flat A M _ _
      (Module.compHom _ (g.stalkMap (i x)).hom)
    change @Module.Flat A M _ _ (Module.compHom _ ((i ≫ g).stalkMap x).hom) at hflat
    rwa [Scheme.Hom.stalkMap_comp] at hflat
  obtain ⟨e⟩ := AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
    i x hi F
  let eₗ : M ≃ₗ[B] Q := e.toLinearEquiv
  change Module.Flat A Q
  exact Module.Flat.of_linearEquiv (eₗ.restrictScalars A).symm

private lemma isFlatOverAt_pushforward_of_isClosedImmersion
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ S)
    (x : X) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : AlgebraicGeometry.IsFlatOverAt (i ≫ g).toLRSHom.toShHom F x) :
    AlgebraicGeometry.IsFlatOverAt g.toLRSHom.toShHom
      ((Scheme.Modules.pushforward i).obj F) (i x) :=
  isFlatOverAt_pushforward_of_finite_singleton_fiber i g x
    (Set.ext fun _ => (IsClosedImmersion.isClosedEmbedding i).injective.eq_iff) F hflat

/-- Sections of a pushforward over an open are the sections on its inverse image, with scalars
restricted along the structure morphism: the identification is the identity on sections. This is
the underived half of Stacks 01EZ. -/
private def pushforwardSectionsLinearEquiv {Z Y : Scheme.{u}} (i : Z ⟶ Y) (G : Z.Modules)
    (W : Y.Opens) :
    letI : Module Γ(Y, W) Γ(G, i ⁻¹ᵁ W) := Module.compHom _ (i.app W).hom
    Γ(G, i ⁻¹ᵁ W) ≃ₗ[Γ(Y, W)] Γ((Scheme.Modules.pushforward i).obj G, W) :=
  letI : Module Γ(Y, W) Γ(G, i ⁻¹ᵁ W) := Module.compHom _ (i.app W).hom
  { toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private lemma free_sections_of_pushforward
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (R : CommRingCat.{u}) (b : Y ⟶ Spec R)
    (G : Z.Modules) (M : Y.Modules)
    (e : M ≅ (Scheme.Modules.pushforward i).obj G)
    (W : Y.Opens)
    (hfree : letI : Module R Γ(M, W) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ b.appLE ⊤ W (le_preimage_top _ _)).hom
      Module.Free R Γ(M, W)) :
    letI : Module R Γ(G, i ⁻¹ᵁ W) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫
        (i ≫ b).appLE ⊤ (i ⁻¹ᵁ W) (le_preimage_top _ _)).hom
    Module.Free R Γ(G, i ⁻¹ᵁ W) := by
  let β := (Scheme.ΓSpecIso R).inv ≫ b.appLE ⊤ W (le_preimage_top _ _)
  let α := (Scheme.ΓSpecIso R).inv ≫
    (i ≫ b).appLE ⊤ (i ⁻¹ᵁ W) (le_preimage_top _ _)
  have hiapp : i.appLE W (i ⁻¹ᵁ W) le_rfl = i.app W := by
    simp [Scheme.Hom.appLE]
  have hα : β ≫ i.app W = α := by
    dsimp [α, β]
    rw [← hiapp, Category.assoc, Scheme.Hom.appLE_comp_appLE]
  let : Algebra R Γ(Y, W) := β.hom.toAlgebra
  let : Module R Γ((Scheme.Modules.pushforward i).obj G, W) := Module.compHom _ β.hom
  have : Module.Free R Γ((Scheme.Modules.pushforward i).obj G, W) :=
    free_sections_of_iso e W β hfree
  let : Module Γ(Y, W) Γ(G, i ⁻¹ᵁ W) :=
    Module.compHom _ (i.app W).hom
  let : Module R Γ(G, i ⁻¹ᵁ W) :=
    Module.compHom _ (β ≫ i.app W).hom
  have : IsScalarTower R Γ(Y, W) Γ(G, i ⁻¹ᵁ W) := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower R Γ(Y, W) Γ((Scheme.Modules.pushforward i).obj G, W) :=
    IsScalarTower.of_compHom _ _ _
  have hsource : Module.Free R Γ(G, i ⁻¹ᵁ W) :=
    Module.Free.of_equiv ((pushforwardSectionsLinearEquiv i G W).restrictScalars R).symm
  change @Module.Free R Γ(G, i ⁻¹ᵁ W) _ _ (Module.compHom _ α.hom)
  rwa [← hα]

/-- Flatness of `F` over `S` at a point of an open `V` transfers to the pushforward of `F|_V`
along a closed immersion `i` over `S`. -/
private lemma isFlatOverAt_pushforward_of_comp_eq
    {X S A : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens)
    (i : V.toScheme ⟶ A) [IsClosedImmersion i] (p : A ⟶ S) (hcomp : i ≫ p = V.ι ≫ f)
    (x : V.toScheme) (hflat : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F (V.ι x)) :
    AlgebraicGeometry.IsFlatOverAt p.toLRSHom.toShHom
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback V.ι).obj F)) (i x) := by
  have := isQuasicoherent_pullback V.ι F
  refine isFlatOverAt_pushforward_of_isClosedImmersion i p x _ ?_
  rw [hcomp]
  exact (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt V.ι f F x (by
    change (V.ι.stalkMap x).hom.Flat
    exact Flat.stalkMap V.ι x)).mp hflat

/-- When `i ≫ p = v ≫ f` with `v` an open immersion, the base change of `i` to `B` maps to
`X ×_S B` by an open immersion compatible with both projections. -/
private lemma exists_isOpenImmersion_pullback_of_comp_eq {V X A S B : Scheme.{u}}
    (v : V ⟶ X) [IsOpenImmersion v] (f : X ⟶ S) (i : V ⟶ A) (p : A ⟶ S) (b : B ⟶ S)
    (hcomp : i ≫ p = v ≫ f) :
    ∃ k : pullback i (pullback.fst p b) ⟶ pullback f b, IsOpenImmersion k ∧
      k ≫ pullback.fst f b = pullback.fst i (pullback.fst p b) ≫ v ∧
      k ≫ pullback.snd f b = pullback.snd i (pullback.fst p b) ≫ pullback.snd p b := by
  let a₀ := pullback.fst i (pullback.fst p b)
  let eC : pullback i (pullback.fst p b) ≅ pullback (v ≫ f) b :=
    pullbackRightPullbackFstIso p b i ≪≫ pullback.congrHom hcomp rfl
  let eO : pullback v (pullback.fst f b) ≅ pullback (v ≫ f) b :=
    pullbackRightPullbackFstIso f b v
  let eQ := eO ≪≫ eC.symm
  let kQ := pullback.snd v (pullback.fst f b)
  have hk : IsOpenImmersion (eQ.inv ≫ kQ) := by
    dsimp [kQ]
    infer_instance
  have heCfst : eC.hom ≫ pullback.fst (v ≫ f) b = a₀ := by
    dsimp [eC, a₀]
    simp only [Category.assoc, pullback.congrHom_hom,
      pullback.map, pullback.lift_fst, Category.comp_id]
    simp
  have heCfstInv : eC.inv ≫ a₀ = pullback.fst (v ≫ f) b := by
    calc
      eC.inv ≫ a₀ = eC.inv ≫ eC.hom ≫ pullback.fst (v ≫ f) b := by rw [heCfst]
      _ = pullback.fst (v ≫ f) b := by simp
  have heQfst : eQ.hom ≫ a₀ = pullback.fst v (pullback.fst f b) := by
    dsimp [eQ]
    calc
      eO.hom ≫ eC.inv ≫ a₀ = eO.hom ≫ pullback.fst (v ≫ f) b := by rw [heCfstInv]
      _ = pullback.fst v (pullback.fst f b) := by
        dsimp [eO]
        simp
  have hkQfst : kQ ≫ pullback.fst f b = pullback.fst v (pullback.fst f b) ≫ v := by
    dsimp [kQ]
    exact (pullback.condition).symm
  have hkX : (eQ.inv ≫ kQ) ≫ pullback.fst f b = a₀ ≫ v := by
    rw [Category.assoc, hkQfst, ← heQfst]
    simp
  have hkB : (eQ.inv ≫ kQ) ≫ pullback.snd f b =
      pullback.snd i (pullback.fst p b) ≫ pullback.snd p b := by
    dsimp [eQ, eC, eO, kQ]
    simp [Category.assoc, pullback.map,
      pullbackRightPullbackFstIso_inv_snd_snd,
      pullbackRightPullbackFstIso_hom_snd]
  exact ⟨eQ.inv ≫ kQ, hk, hkX, hkB⟩

/-- **Stacks Project, Tag 05MF.** A finite-type quasi-coherent module which is flat over the
base at a point has free sections on an affine neighbourhood of the lifted point after base
change to the local scheme of an affine elementary étale neighbourhood. -/
@[stacks 05MF]
public theorem exists_elementaryEtaleNeighborhood_free_sections_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Free (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  classical
  obtain ⟨V, hx, A, hA, i, p, hi, hp, hcomp⟩ :=
    exists_closedImmersion_affineSpace_of_locallyOfFiniteType f x
  let : IsClosedImmersion i := hi
  let : LocallyOfFinitePresentation p := hp
  let FV := (Scheme.Modules.pullback V.1.ι).obj F
  have : FV.IsQuasicoherent := isQuasicoherent_pullback V.1.ι F
  have : FV.IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType V.1.ι.toLRSHom.toShHom F
  let G := (Scheme.Modules.pushforward i).obj FV
  have : IsAffineHom i := inferInstance
  have : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom i FV
  have : G.IsFiniteType :=
    Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward i FV
  let xv : V.1.toScheme := ⟨x, hx⟩
  have hxv : V.1.ι xv = x := rfl
  have hpoint : p (i xv) = f x := by
    have h := congrArg (fun k : V.1.toScheme ⟶ S => k xv) hcomp
    simpa only [Scheme.Hom.comp_apply, hxv] using h
  have hresult := exists_free_sections_of_locallyFinitePresentation p G (i xv)
    (isFlatOverAt_pushforward_of_comp_eq f F V.1 i p hcomp xv (by simpa only [hxv] using hflat))
  rw [hpoint] at hresult
  obtain ⟨N, hN, hNA, y, W, hyA, hyN, hyB, hW, hyW, hfree⟩ := hresult
  let b : Spec (N.scheme.presheaf.stalk N.point) ⟶ S :=
    N.scheme.fromSpecStalk N.point ≫ N.toBase
  let T := pullback f b
  let R₀ := pullback i (pullback.fst p b)
  let i₀ : R₀ ⟶ pullback p b := pullback.snd i (pullback.fst p b)
  let a₀ : R₀ ⟶ V.1.toScheme := pullback.fst i (pullback.fst p b)
  obtain ⟨k, hk, hkX, hkB⟩ : ∃ k : R₀ ⟶ T, IsOpenImmersion k ∧
      k ≫ pullback.fst f b = a₀ ≫ V.1.ι ∧ k ≫ pullback.snd f b = i₀ ≫ pullback.snd p b :=
    exists_isOpenImmersion_pullback_of_comp_eq V.1.ι f i p b hcomp
  have : IsClosedImmersion i₀ := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback i (pullback.fst p b)) hi
  let H₀ := (Scheme.Modules.pullback a₀).obj FV
  let W₀ : R₀.Opens := i₀ ⁻¹ᵁ W
  obtain ⟨r₀, hrX, hrY⟩ := Scheme.Pullback.exists_preimage_pullback xv y hyA.symm
  refine ⟨N, hN, hNA, k r₀, k ''ᵁ W₀, ?_, ?_, (hW.preimage i₀).image_of_isOpenImmersion k,
    ⟨r₀, by change i₀ r₀ ∈ W; rwa [hrY], rfl⟩, ?_⟩
  · have h := congrArg (fun m : R₀ ⟶ X => m r₀) hkX
    change pullback.fst f b (k r₀) = V.1.ι (a₀ r₀) at h
    rwa [hrX, hxv] at h
  · have h := congrArg (fun m : R₀ ⟶ Spec (N.scheme.presheaf.stalk N.point) => m r₀) hkB
    change pullback.snd f b (k r₀) = pullback.snd p b (i₀ r₀) at h
    rw [h, hrY, hyB, Scheme.fromSpecStalk_closedPoint]
  · let H := (Scheme.Modules.pullback (pullback.fst f b)).obj F
    let eH : (Scheme.Modules.pullback k).obj H ≅ H₀ :=
      (Scheme.Modules.pullbackComp k (pullback.fst f b)).app F ≪≫
        (Scheme.Modules.pullbackCongr hkX).app F ≪≫
        ((Scheme.Modules.pullbackComp a₀ V.1.ι).app F).symm
    exact free_sections_image_of_isOpenImmersion_of_iso k
      (.of (N.scheme.presheaf.stalk N.point)) (pullback.snd f b) _ hkB H H₀ eH.symm W₀
      (free_sections_of_pushforward i₀ _ (pullback.snd p b) H₀ _
        (affinePushforwardBaseChangeIso (IsPullback.of_hasPullback i (pullback.fst p b)) FV)
        W hfree)

end AlgebraicGeometry

end
