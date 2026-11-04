module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineAlgebraicSpaceOverIntersection
public import StacksFrontier.AlgebraicGeometry.Quot.AffineRepresentedLocal
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomAffineLocal
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFinitePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSourcePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AssemblyGeneratedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteFiniteCoproductsClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AssemblyOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
import all StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# The first assertion of Stacks 08K6 from the second

In Situation 08JT let `f` be of finite presentation and `G` of finite presentation, flat over the
base, with support proper over it, and let `F` be a quasi-coherent module étale-locally generated
by fewer than `μ` sections, for one cardinal `μ` below the cutoff of the site.  If the relative
Hom functor out of every module of finite presentation is an algebraic space affine and of finite
presentation over the base (the second assertion of Stacks 08K6), then `Hom(F, G)` is an algebraic
space affine over the base.

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `exists_moduleHomOverPrecomp_app_eq`: a homomorphism out of the pullback of the colimit of the
  generators killing all relations comes from `F`.
* `isAffineAlgebraicSpaceOver_baseChangeHomFunctor_of_relations` and
  `isAffineRepresentedOver_baseChangeHomFunctor_of_relations`: the relative Hom functor out of a
  module given by generators and relations is an algebraic space affine over an affine base,
  represented by an affine scheme of bounded size.
* `isAffineRepresentedOver_baseChangeHomFunctor_colimit_partialSums`: the relative Hom functor out
  of a direct sum of boundedly many modules is represented by an affine scheme of bounded size.
* `isAffineRepresentedOver_baseChangeHomFunctor_of_isEtaleLocallyGeneratedBelow`: over an affine
  scheme `Z`, `Hom(F, G)` is represented by an affine scheme of size at most
  `2 ^ 2 ^ max (max μ ℵ₀) (size Z)`.
* `HomSituation.isAffineAlgebraicSpaceOverBase_of_isEtaleLocallyGeneratedBelow`: `Hom(F, G)` is an
  algebraic space affine over the base.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

open HomSituation CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section BaseChangeHom

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hc : ModulePushforwardCoherence B S hS)
  (G : Modules.{u, u} B S hS X.1 X.2)

/-- The relative Hom functor out of a module `M` on `X`, into `G`, on the test schemes over
`Y`. -/
abbrev baseChangeHomFunctor (M : Modules.{u, u} B S hS X.1 X.2) :
    (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  (baseChangeOver f).op ⋙ moduleHomOver hc M G

/-- Precomposition with a morphism of source modules, between the relative Hom functors. -/
abbrev baseChangeHomFunctorMap {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M') :
    baseChangeHomFunctor f hc G M' ⟶ baseChangeHomFunctor f hc G M :=
  Functor.whiskerLeft (baseChangeOver f).op (moduleHomOverPrecomp hc φ G)

/-- Precomposition with a composite is the composite of the precompositions, in the opposite
order. -/
theorem baseChangeHomFunctorMap_comp {M M' M'' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M')
    (ψ : M' ⟶ M'') :
    baseChangeHomFunctorMap f hc G (φ ≫ ψ) =
      baseChangeHomFunctorMap f hc G ψ ≫ baseChangeHomFunctorMap f hc G φ :=
  (congrArg (Functor.whiskerLeft (baseChangeOver f).op)
    (moduleHomOverPrecomp_comp hc φ ψ G)).trans (Functor.whiskerLeft_comp _ _ _)

end BaseChangeHom

/-- The pullback of modules along a morphism of algebraic spaces is a left adjoint. -/
private instance isLeftAdjoint_modulePullback_aux {W X : AlgebraicSpaces B S hS} (q : W ⟶ X) :
    (modulePullback B S hS q).IsLeftAdjoint :=
  ⟨_, ⟨modulePullbackAdjunction B S hS q⟩⟩

section OverLevel

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 6000] hasCoproduct_of_hasBiproduct

variable {X : AlgebraicSpaces B S hS} (hc : ModulePushforwardCoherence B S hS)
  (G : Modules.{u, u} B S hS X.1 X.2)

/-- Precomposition with an epimorphism of source modules is injective on the relative Hom
functor. -/
theorem injective_moduleHomOverPrecomp_app {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M')
    [Epi φ] (Z : (Over X)ᵒᵖ) : Function.Injective ((moduleHomOverPrecomp hc φ G).app Z) := by
  intro a b hab
  rw [moduleHomOverPrecomp_app_apply, moduleHomOverPrecomp_app_apply] at hab
  exact (cancel_epi _).1 hab

variable {I : Type u} [SmallCategory I] [IsFiltered I] (E : I ⥤ Modules.{u, u} B S hS X.1 X.2)
  {F : Modules.{u, u} B S hS X.1 X.2} (π : E ⟶ (Functor.const I).obj F)
  (hπ : ∀ {N : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ N), (∀ i, π.app i ≫ g = 0) → g = 0)
  {R : I → Type u} (P : ∀ i, R i → Modules.{u, u} B S hS X.1 X.2) (κ : ∀ i r, P i r ⟶ E.obj i)
  (hκπ : ∀ i r, κ i r ≫ π.app i = 0)
  (hκ : ∀ i {N : Modules.{u, u} B S hS X.1 X.2} (g : kernel (π.app i) ⟶ N),
    (∀ r, kernel.lift (π.app i) (κ i r) (hκπ i r) ≫ g = 0) → g = 0)
  [HasColimit E]

/-- A finite direct sum of modules of finite presentation on an algebraic space is of finite
presentation. -/
theorem isFinitePresentationOnSite_sigma {ι : Type u} [Finite ι]
    (M : ι → Modules.{u, u} B S hS X.1 X.2) (h : ∀ i, (M i).IsFinitePresentationOnSite) :
    (∐ M).IsFinitePresentationOnSite :=
  @SheafOfModules.isFinitePresentationOnSite_coproduct _ _ _ _ inferInstance
    (Abelian.hasZeroObject) (@hasFiniteCoproducts_of_hasFiniteBiproducts _ _ _
      Abelian.hasFiniteBiproducts) ι _ M _ h

/-- The direct sum of the sources of finitely many relations. -/
noncomputable abbrev relSource (𝒮 : Finset (Σ i, R i)) : Modules.{u, u} B S hS X.1 X.2 :=
  ∐ fun x : 𝒮 => P x.1.1 x.1.2

omit [SmallCategory I] [IsFiltered I] in
/-- The direct sum of the sources of finitely many relations is of finite presentation when each
source is. -/
theorem isFinitePresentationOnSite_relSource (h : ∀ i r, (P i r).IsFinitePresentationOnSite)
    (𝒮 : Finset (Σ i, R i)) : (relSource P 𝒮).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_sigma _ fun x => h x.1.1 x.1.2


/-- The morphism from the direct sum of the sources of finitely many relations to the colimit of
the system. -/
noncomputable def relMap (𝒮 : Finset (Σ i, R i)) : relSource P 𝒮 ⟶ colimit E :=
  Sigma.desc fun x => κ x.1.1 x.1.2 ≫ colimit.ι E x.1.1

/-- The inclusion of the source of one relation into the direct sum. -/
noncomputable def relι (𝒮 : Finset (Σ i, R i)) (x : 𝒮) : P x.1.1 x.1.2 ⟶ relSource P 𝒮 :=
  Sigma.ι (fun x : 𝒮 => P x.1.1 x.1.2) x

omit [IsFiltered I] in
/-- The map out of the direct sum of the sources of the relations, on the source of one relation:
the relation followed by the colimit inclusion. -/
theorem relι_relMap (𝒮 : Finset (Σ i, R i)) (x : 𝒮) :
    relι P 𝒮 x ≫ relMap E P κ 𝒮 = κ x.1.1 x.1.2 ≫ colimit.ι E x.1.1 := by
  simp [relι, relMap]

/-- The inclusion of the direct sum over a smaller set of relations. -/
noncomputable def relIncl {𝒮 𝒮' : Finset (Σ i, R i)} (h : 𝒮 ⊆ 𝒮') :
    relSource P 𝒮 ⟶ relSource P 𝒮' :=
  Sigma.desc fun x => Sigma.ι (fun x : 𝒮' => P x.1.1 x.1.2) ⟨x.1, h x.2⟩

omit [IsFiltered I] in
/-- The maps out of the direct sums of the sources of the relations are compatible with the
inclusion of a smaller set of relations. -/
theorem relIncl_relMap {𝒮 𝒮' : Finset (Σ i, R i)} (h : 𝒮 ⊆ 𝒮') :
    relIncl P h ≫ relMap E P κ 𝒮' = relMap E P κ 𝒮 :=
  Sigma.hom_ext _ _ fun x => by simp [relIncl, relMap]

/-- The morphism from the colimit of the system to `F`. -/
noncomputable def colimitToTarget : colimit E ⟶ F := colimit.desc E ⟨F, π⟩

omit [IsFiltered I] in
include hκπ in
/-- The relations are killed by the morphism from the colimit of the system to `F`. -/
theorem relMap_colimitToTarget (𝒮 : Finset (Σ i, R i)) :
    relMap E P κ 𝒮 ≫ colimitToTarget E π = 0 :=
  Sigma.hom_ext _ _ fun x => by simp [relMap, colimitToTarget, hκπ]

omit [IsFiltered I] in
include hπ in
/-- The morphism from the colimit of the system to `F` is an epimorphism when the morphisms
`π i` are jointly epimorphic. -/
theorem epi_colimitToTarget : Epi (colimitToTarget E π) := by
  refine Preadditive.epi_of_cancel_zero _ fun {N} g hg => hπ g fun i => ?_
  have := colimit.ι E i ≫= hg
  rwa [comp_zero, ← Category.assoc, colimitToTarget, colimit.ι_desc] at this

omit [SmallCategory I] [IsFiltered I] in
/-- If `c = a ≫ b`, `b ≫ y = z ≫ y` and `z = 0`, then `c ≫ y = 0`. -/
theorem comp_eq_zero_of_comp_eq {C : Type*} [Category C] [HasZeroMorphisms C] {A₀ A₁ A₂ A₃ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₀ ⟶ A₂) (y : A₂ ⟶ A₃) (hc : c = a ≫ b) {z : A₁ ⟶ A₂}
    (h : b ≫ y = z ≫ y) (hz : z = 0) : c ≫ y = 0 := by
  rw [hc, Category.assoc, h, hz, zero_comp, comp_zero]

include hπ hκ in
/-- A homomorphism out of the pullback of the colimit killing the pullbacks of all relations
factors through the pullback of `F`. -/
theorem exists_modulePullback_map_colimitToTarget_comp {W : AlgebraicSpaces B S hS} (q : W ⟶ X)
    {N : Modules.{u, u} B S hS W.1 W.2}
    (ψ : (modulePullback B S hS q).obj (colimit E) ⟶ N)
    (hψ : ∀ i r, (modulePullback B S hS q).map (κ i r ≫ colimit.ι E i) ≫ ψ = 0) :
    ∃ φ, (modulePullback B S hS q).map (colimitToTarget E π) ≫ φ = ψ := by
  have hpres : PreservesColimitsOfSize.{u, u} (modulePullback B S hS q) :=
    (modulePullbackAdjunction B S hS q).leftAdjoint_preservesColimits
  have hcol := isColimitOfPreserves (modulePullback B S hS q) (colimit.isColimit E)
  obtain ⟨φ₀, hφ₀, -⟩ := existsUnique_modulePullback_desc_of_relations E π hπ P κ hκπ hκ q N
    (fun i => (modulePullback B S hS q).map (colimit.ι E i) ≫ ψ)
    (fun {i j} f => by
      rw [← Category.assoc, ← Functor.map_comp, colimit.w])
    (fun i r => by
      rw [← Category.assoc, ← Functor.map_comp]
      exact hψ i r)
  refine ⟨φ₀, hcol.hom_ext fun i => ?_⟩
  rw [Functor.mapCocone_ι_app, ← Category.assoc, ← Functor.map_comp, colimitToTarget,
    colimit.cocone_ι, colimit.ι_desc]
  exact hφ₀ i

include hπ hκ in
/-- On the relative Hom functor, the homomorphisms out of the pullback of the colimit killing all
relations are those coming from `F`. -/
theorem exists_moduleHomOverPrecomp_app_eq (Z : (Over X)ᵒᵖ)
    (y : (moduleHomOver hc (colimit E) G).obj Z)
    (hy : ∀ 𝒮 : Finset (Σ i, R i), (moduleHomOverPrecomp hc (relMap E P κ 𝒮) G).app Z y =
      (moduleHomOverPrecomp hc (0 : relSource P 𝒮 ⟶ colimit E) G).app Z y) :
    ∃ x, (moduleHomOverPrecomp hc (colimitToTarget E π) G).app Z x = y := by
  have hψ : ∀ i r, (modulePullback B S hS Z.unop.hom).map (κ i r ≫ colimit.ι E i) ≫ y = 0 := by
    intro i r
    have h := hy {⟨i, r⟩}
    rw [moduleHomOverPrecomp_app_apply, moduleHomOverPrecomp_app_apply] at h
    have hι : (modulePullback B S hS Z.unop.hom).map (κ i r ≫ colimit.ι E i) =
        (modulePullback B S hS Z.unop.hom).map
          (relι P {⟨i, r⟩} ⟨⟨i, r⟩, Finset.mem_singleton_self _⟩) ≫
          (modulePullback B S hS Z.unop.hom).map (relMap E P κ {⟨i, r⟩}) := by
      rw [← Functor.map_comp, relι_relMap]
    have hz : (modulePullback B S hS Z.unop.hom).map (0 : relSource P {⟨i, r⟩} ⟶ colimit E) =
      0 := Functor.map_zero _ _ _
    exact comp_eq_zero_of_comp_eq _ _ _ y hι h hz
  obtain ⟨φ₀, hφ₀⟩ := exists_modulePullback_map_colimitToTarget_comp E π hπ P κ hκπ hκ Z.unop.hom
    y hψ
  exact ⟨φ₀, (moduleHomOverPrecomp_app_apply hc _ G Z φ₀).trans hφ₀⟩

end OverLevel

section Core

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 6000] hasCoproduct_of_hasBiproduct

variable (hc : ModulePushforwardCoherence B S hS) {T : BigFppfOver B S hS}
  (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (schemeSpaceFunctor B S hS).obj T) (G : Modules.{u, u} B S hS X.1 X.2)
  {I : Type u} [SmallCategory I] [IsFiltered I] (E : I ⥤ Modules.{u, u} B S hS X.1 X.2)
  {F : Modules.{u, u} B S hS X.1 X.2} (π : E ⟶ (Functor.const I).obj F)
  (hπ : ∀ {N : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ N), (∀ i, π.app i ≫ g = 0) → g = 0)
  {R : I → Type u} (P : ∀ i, R i → Modules.{u, u} B S hS X.1 X.2) (κ : ∀ i r, P i r ⟶ E.obj i)
  (hκπ : ∀ i r, κ i r ≫ π.app i = 0)
  (hκ : ∀ i {N : Modules.{u, u} B S hS X.1 X.2} (g : kernel (π.app i) ⟶ N),
    (∀ r, kernel.lift (π.app i) (κ i r) (hκπ i r) ≫ g = 0) → g = 0)
  [HasColimit E]

include hT hπ hκ in
/-- The relative Hom functor out of a module given by generators and relations is an algebraic
space affine over an affine base, as soon as the relative Hom functors out of the colimit of the
generators and out of the finite direct sums of the sources of the relations are. -/
theorem isAffineAlgebraicSpaceOver_baseChangeHomFunctor_of_relations
    (hL : IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T)
      (baseChangeHomFunctor f hc G (colimit E)))
    (hQ : ∀ 𝒮 : Finset (Σ i, R i), IsAffineAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj T) (baseChangeHomFunctor f hc G (relSource P 𝒮))) :
    IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T)
      (baseChangeHomFunctor f hc G F) := by
  have := epi_colimitToTarget E π hπ
  have hα : ∀ {𝒮 𝒮' : Finset (Σ i, R i)} (h : 𝒮 ⊆ 𝒮') (a : relSource P 𝒮 ⟶ colimit E)
      (b : relSource P 𝒮' ⟶ colimit E), relIncl P h ≫ b = a →
      baseChangeHomFunctorMap f hc G a =
        baseChangeHomFunctorMap f hc G b ≫ baseChangeHomFunctorMap f hc G (relIncl P h) := by
    rintro 𝒮 𝒮' h a b rfl
    rw [baseChangeHomFunctorMap_comp]
  have hmono : ∀ {𝒮 𝒮' : Finset (Σ i, R i)}, 𝒮 ⊆ 𝒮' → ∀ W
      (y : (baseChangeHomFunctor f hc G (colimit E)).obj W),
      (baseChangeHomFunctorMap f hc G (relMap E P κ 𝒮')).app W y =
        (baseChangeHomFunctorMap f hc G (0 : relSource P 𝒮' ⟶ colimit E)).app W y →
      (baseChangeHomFunctorMap f hc G (relMap E P κ 𝒮)).app W y =
        (baseChangeHomFunctorMap f hc G (0 : relSource P 𝒮 ⟶ colimit E)).app W y := by
    intro 𝒮 𝒮' h W y hy
    rw [hα h _ _ (relIncl_relMap E P κ h), hα h 0 0 comp_zero, NatTrans.comp_app_apply,
      NatTrans.comp_app_apply, hy]
  refine isAffineAlgebraicSpaceOver_of_injective_of_forall_eq B S hS hT
    (fun 𝒮 => baseChangeHomFunctor f hc G (relSource P 𝒮))
    (fun 𝒮 => baseChangeHomFunctorMap f hc G (relMap E P κ 𝒮))
    (fun 𝒮 => baseChangeHomFunctorMap f hc G (0 : relSource P 𝒮 ⟶ colimit E))
    hmono B.contains_terminal hL hQ
    (baseChangeHomFunctorMap f hc G (colimitToTarget E π))
    (fun W => injective_moduleHomOverPrecomp_app hc G (colimitToTarget E π) _)
    (fun W y hy => exists_moduleHomOverPrecomp_app_eq hc G E π hπ P κ hκπ hκ _ y hy)
    (fun 𝒮 => ?_)
  rw [← baseChangeHomFunctorMap_comp, ← baseChangeHomFunctorMap_comp,
    relMap_colimitToTarget E π P κ hκπ, zero_comp]

include hT hπ hκ in
/-- If the relative Hom functor out of the colimit of the generators is represented by an affine
scheme of size at most `κ₀`, the relative Hom functor out of the module is represented by an
affine scheme of size at most `2 ^ 2 ^ κ₀`. -/
theorem isAffineRepresentedOver_baseChangeHomFunctor_of_relations {κ₀ : Cardinal.{u}}
    (hL : IsAffineRepresentedOver T κ₀ (baseChangeHomFunctor f hc G (colimit E)))
    (hQ : ∀ 𝒮 : Finset (Σ i, R i), IsAffineAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj T) (baseChangeHomFunctor f hc G (relSource P 𝒮))) :
    IsAffineRepresentedOver T ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ₀)
      (baseChangeHomFunctor f hc G F) :=
  have := epi_colimitToTarget E π hπ
  IsAffineRepresentedOver.of_injective hT
    (isAffineAlgebraicSpaceOver_baseChangeHomFunctor_of_relations hc hT f G E π hπ P κ hκπ hκ
      (hL.isAffineAlgebraicSpaceOver hT) hQ) hL
    (baseChangeHomFunctorMap f hc G (colimitToTarget E π))
    (fun _ => injective_moduleHomOverPrecomp_app hc G (colimitToTarget E π) _)

end Core

section Generators

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 6000] hasCoproduct_of_hasBiproduct

variable {X : AlgebraicSpaces B S hS} {A : Type u} (Gs : A → Modules.{u, u} B S hS X.1 X.2)

/-- The finite partial direct sums of a family of modules, with the inclusions as transition
maps. -/
def partialSums : Finset (Discrete A) ⥤ Modules.{u, u} B S hS X.1 X.2 where
  obj J := ∐ fun x : J => Gs x.1.as
  map {J J'} h := Sigma.desc fun x => Sigma.ι (fun x : J' => Gs x.1.as) ⟨x.1, h.down.down x.2⟩
  map_id J := Sigma.hom_ext _ _ fun x => by simp
  map_comp f g := Sigma.hom_ext _ _ fun x => by simp

/-- The partial direct sum over a finite set `J` is the direct sum of the modules indexed by
`J`. -/
theorem partialSums_obj (J : Finset (Discrete A)) :
    (partialSums Gs).obj J = ∐ fun x : J => Gs x.1.as := rfl

/-- The morphisms out of the finite partial direct sums induced by a family of morphisms. -/
def partialSumsDesc {F : Modules.{u, u} B S hS X.1 X.2} (ps : ∀ a, Gs a ⟶ F) :
    partialSums Gs ⟶ (Functor.const (Finset (Discrete A))).obj F where
  app J := Sigma.desc fun x => ps x.1.as
  naturality J J' h := Sigma.hom_ext _ _ fun x => by simp [partialSums]

/-- A morphism killed by the family `ps` is killed by the induced morphisms out of the partial
sums, and conversely. -/
theorem eq_zero_of_partialSumsDesc_comp {F : Modules.{u, u} B S hS X.1 X.2} (ps : ∀ a, Gs a ⟶ F)
    (hps : ∀ {N : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ N), (∀ a, ps a ≫ g = 0) → g = 0)
    {N : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ N)
    (hg : ∀ J, (partialSumsDesc Gs ps).app J ≫ g = 0) : g = 0 := by
  refine hps g fun a => ?_
  have hι : Sigma.ι (fun x : ({⟨a⟩} : Finset (Discrete A)) => Gs x.1.as)
      ⟨⟨a⟩, Finset.mem_singleton_self _⟩ ≫ (partialSumsDesc Gs ps).app {⟨a⟩} = ps a := by
    simp [partialSumsDesc]
  rw [← hι]
  exact (Category.assoc _ _ _).trans ((congrArg _ (hg _)).trans comp_zero)

variable (hc : ModulePushforwardCoherence B S hS) {T : BigFppfOver B S hS}
  (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (f : X ⟶ (schemeSpaceFunctor B S hS).obj T) (G : Modules.{u, u} B S hS X.1 X.2)

/-- The kernels of the finite partial sums of generators are generated by modules of finite
presentation. -/
theorem exists_relations_partialSumsDesc (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (ps : ∀ a, Gs a ⟶ F)
    (hE : ∀ J : Finset (Discrete A), ((partialSums Gs).obj J).IsFinitePresentationOnSite)
    (J : Finset (Discrete A)) :
    ∃ (R : Type u) (P : R → Modules.{u, u} B S hS X.1 X.2)
      (κ : ∀ r, P r ⟶ (partialSums Gs).obj J)
      (hκπ : ∀ r, κ r ≫ (partialSumsDesc Gs ps).app J = 0),
      (∀ r, (P r).IsFinitePresentationOnSite) ∧
        ∀ {N : Modules.{u, u} B S hS X.1 X.2} (g : kernel ((partialSumsDesc Gs ps).app J) ⟶ N),
          (∀ r, kernel.lift _ (κ r) (hκπ r) ≫ g = 0) → g = 0 := by
  have := hE J
  have : (((Functor.const (Finset (Discrete A))).obj F).obj J).IsQuasicoherentOnSite := hF
  have hK := isQuasicoherentOnSite_kernel_of_quasicoherent B S hS X.1 X.2
    ((partialSumsDesc Gs ps).app J)
  obtain ⟨Iᵣ, _, -, D, φ, hD, ⟨hcol⟩⟩ :=
    exists_isFilteredColimit_isFinitePresentationOnSite B S hS B.contains_terminal X.2 hqc hqs _ hK
  refine ⟨Iᵣ, D.obj, fun r => φ.app r ≫ kernel.ι _, fun r => by simp, hD,
    fun {N} g hg => hcol.hom_ext fun r => ?_⟩
  have h1 : kernel.lift _ (φ.app r ≫ kernel.ι _) (by simp) = φ.app r :=
    (cancel_mono (kernel.ι _)).1 (by rw [kernel.lift_ι])
  simpa [h1] using hg r

include hT in
/-- The relative Hom functor out of a direct sum of a family of at most `λ` modules, each with an
affine relative Hom functor of finite presentation over an affine scheme `T`, is represented by
an affine scheme of size at most `max λ (size T)`. -/
theorem isAffineRepresentedOver_baseChangeHomFunctor_colimit_partialSums
    (hb : ∀ J : Finset (Discrete A), IsAffineFinitePresentationAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj T) (baseChangeHomFunctor f hc G ((partialSums Gs).obj J)))
    {lam : Cardinal.{u}} (hlam : lam < B.cutoff) (hA : #A ≤ lam) (h0 : ℵ₀ ≤ lam) :
    IsAffineRepresentedOver T (max lam ((BigFppfOver.toScheme B S hS).obj T).size)
      (baseChangeHomFunctor f hc G (colimit (partialSums Gs))) := by
  have hst : ∀ J : (Finset (Discrete A))ᵒᵖ, IsAffineRepresentedOver T
      ((BigFppfOver.toScheme B S hS).obj T).size
      ((moduleHomOverSystem hc (partialSums Gs) G ⋙
        (Functor.whiskeringLeft _ _ (Type (u + 1))).obj (baseChangeOver f).op).obj J) :=
    fun J => IsAffineRepresentedOver.of_isAffineFinitePresentation hT (hb J.unop)
  have hlim := isLimitOfPreserves
    ((Functor.whiskeringLeft _ _ (Type (u + 1))).obj (baseChangeOver f).op)
    (isLimit_moduleHomOverColimitCone hc (partialSums Gs) G _ (colimit.isColimit _))
  have hI : #((Finset (Discrete A))ᵒᵖ) ≤ lam := by
    rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := Finset (Discrete A))).symm]
    have hfin : #(Finset (Discrete A)) ≤ max Cardinal.aleph0 #(Discrete A) := by
      cases finite_or_infinite (Discrete A) with
      | inl _ => exact (Cardinal.lt_aleph0_of_finite _).le.trans (le_max_left _ _)
      | inr _ => exact (Cardinal.mk_finset_of_infinite _).le.trans (le_max_right _ _)
    refine hfin.trans (max_le h0 ?_)
    rw [Cardinal.mk_congr (⟨Discrete.as, Discrete.mk, fun _ => rfl, fun _ => rfl⟩ :
      Discrete A ≃ A)]
    exact hA
  have hsize : ((BigFppfOver.toScheme B S hS).obj T).size < B.cutoff := T.left.property
  have h := IsAffineRepresentedOver.of_isLimit_of_bounded _ hst
    (max_lt (hI.trans_lt hlam) hsize) _ hlim
  exact h.mono <| max_le (h0.trans (le_max_left _ _)) <| (Cardinal.mul_le_max _ _).trans <|
    max_le (max_le (hI.trans (le_max_left _ _)) (le_max_right _ _)) (h0.trans (le_max_left _ _))

include hT in
/-- Let `f : X ⟶ T` be of finite presentation, with `T` an affine scheme, and let `F` be a
quasi-coherent module étale-locally generated by fewer than `μ` sections, `μ` below the cutoff.
If the relative Hom functors into `G` out of the modules of finite presentation are algebraic
spaces affine and of finite presentation over `T`, then the relative Hom functor out of `F` is
represented by an affine scheme of size at most `2 ^ 2 ^ max (max μ ℵ₀) (size T)`. -/
theorem isAffineRepresentedOver_baseChangeHomFunctor_of_isEtaleLocallyGeneratedBelow
    (hb : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsFinitePresentationOnSite →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T)
        (baseChangeHomFunctor f hc G M))
    (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hgen : IsEtaleLocallyGeneratedBelow B S hS μ F) :
    IsAffineRepresentedOver T ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      max (max μ ℵ₀) ((BigFppfOver.toScheme B S hS).obj T).size)
      (baseChangeHomFunctor f hc G F) := by
  classical
  have hqcT : IsQuasiCompactSpace B S hS ((schemeSpaceFunctor B S hS).obj T).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT
  have hqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS f.hom ((schemeSpaceFunctor B S hS).obj T).2
      hqcT hf
  have hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 :=
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS B.contains_terminal X.2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
        ⟨T, hT, ⟨Iso.refl _⟩⟩) hf
  have hM := isLocallyFpGenerated_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hqc hqs F hF
  obtain ⟨A, Gs, hGs, ps, hA, hps⟩ :=
    exists_isFinitePresentation_family_of_isEtaleLocallyGeneratedBelow B S hS X.2 hqc F hM hgen
  have hGs' : ∀ a, (Gs a).IsFinitePresentationOnSite := fun a =>
    have := hGs a
    FpAssembly.isFinitePresentationOnSite_of_isFinitePresentation (Gs a)
  have hE : ∀ J : Finset (Discrete A), ((partialSums Gs).obj J).IsFinitePresentationOnSite :=
    fun J => isFinitePresentationOnSite_sigma _ fun x => hGs' x.1.as
  have hrel := exists_relations_partialSumsDesc Gs hqc hqs F hF ps hE
  choose R P κ hκπ hP hκ using hrel
  have hQ : ∀ 𝒮 : Finset (Σ J, R J), IsAffineAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj T) (baseChangeHomFunctor f hc G (relSource P 𝒮)) :=
    fun 𝒮 => (hb (relSource P 𝒮)
      (isFinitePresentationOnSite_relSource P hP 𝒮)).isAffineAlgebraicSpaceOver
  have hL := isAffineRepresentedOver_baseChangeHomFunctor_colimit_partialSums Gs hc hT f G
    (fun J => hb _ (hE J)) (max_lt hμ B.aleph0_lt_cutoff) hA (le_max_right _ _)
  exact isAffineRepresentedOver_baseChangeHomFunctor_of_relations hc hT f G (partialSums Gs)
    (partialSumsDesc Gs ps) (eq_zero_of_partialSumsDesc_comp Gs ps hps) P κ hκπ hκ hL hQ

end Generators

namespace HomSituation

/-- The relative Hom functor of the situation is the relative Hom functor out of its source
module. -/
theorem homFunctor_eq_baseChangeHomFunctor (s : HomSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) :
    s.homFunctor hc = baseChangeHomFunctor s.f hc s.G s.F :=
  rfl

/-- The situation obtained by replacing the source module by another quasi-coherent module. -/
abbrev withSource (s : HomSituation B S hS) (M : Modules.{u, u} B S hS s.X.1 s.X.2)
    (hM : M.IsQuasicoherentOnSite) : HomSituation B S hS :=
  { s with F := M, quasicoherent_F := hM }

/-- Let `f` be of finite presentation and `G` of finite presentation, flat over the base, with
support proper over the base, and let `F` be étale-locally generated by fewer than `μ` sections
for one cardinal `μ` below the cutoff.  If the relative Hom functor out of every module of finite
presentation is an algebraic space affine and of finite presentation over the base, then
`Hom(F, G)` is an algebraic space affine over the base. -/
theorem isAffineAlgebraicSpaceOverBase_of_isEtaleLocallyGeneratedBelow
    (hb : ∀ v : HomSituation B S hS, IsFinitePresentation B S hS v.f.hom →
      v.F.IsFinitePresentationOnSite → v.G.IsFinitePresentationOnSite →
      IsFlatOver B S hS v.X.2 v.f.hom v.G → HasProperSupportOver v.f v.G →
      v.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS))
    (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)
    (hf : IsFinitePresentation B S hS s.f.hom) (hG : s.G.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) (hproper : HasProperSupportOver s.f s.G)
    (hF : ∃ μ < B.cutoff, IsEtaleLocallyGeneratedBelow B S hS μ s.F) :
    s.IsAffineAlgebraicSpaceOverBase hc := by
  obtain ⟨μ, hμ, hgen⟩ := hF
  refine isAffineAlgebraicSpaceOver_of_isAffineRepresentedOver (s.homFunctor hc)
    (s.isSheaf_homFunctor hc) (max_lt hμ B.aleph0_lt_cutoff) fun Z hZ => ?_
  let p : (schemeSpaceFunctor B S hS).obj Z.left ⟶ s.base := Z.hom
  let t := s.baseChangedSituation p
  have sq : IsPullback (s.baseChangedSourceProjection p) (s.baseChangedMorphism p) s.f p :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS s.f p
  have hft : IsFinitePresentation B S hS t.f.hom :=
    IsFinitePresentation.of_isPullback B S hS (s.baseChangedSource p).2 s.X.2
      ((schemeSpaceFunctor B S hS).obj Z.left).2 s.base.2
      (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hGt : t.G.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B S hS _ _ hG
  have hflatt : IsFlatOver B S hS t.X.2 t.f.hom t.G :=
    isFlatOver_modulePullback_of_isFinitePresentationOnSite B S hS sq s.G hG hflat
  have hpropert : HasProperSupportOver t.f t.G := hproper.of_isPullback sq hG
  have hbt : ∀ M : Modules.{u, u} B S hS t.X.1 t.X.2, M.IsFinitePresentationOnSite →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z.left)
        (baseChangeHomFunctor t.f (modulePushforwardCoherence B S hS) t.G M) :=
    fun M hM => hb (t.withSource M inferInstance) hft hM hGt hflatt hpropert
  have hcore := isAffineRepresentedOver_baseChangeHomFunctor_of_isEtaleLocallyGeneratedBelow
    (modulePushforwardCoherence B S hS) hZ t.f t.G hbt hft t.F t.quasicoherent_F hμ
    (hgen.modulePullback (s.baseChangedSourceProjection p))
  exact hcore.of_iso (s.homFunctorBaseChange p)

end HomSituation

end AlgebraicGeometry.Space

end
