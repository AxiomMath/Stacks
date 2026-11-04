module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful
public import StacksFrontier.Deformation.Artin.FormalObject.OfPredeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Formal.VersalObject.PowerSeriesComparisonHom
public import StacksFrontier.Deformation.VersalRing.Uniqueness

/-!
# The comparison map of versal rings is well defined up to formal homotopy (Stacks 0DR1)

In the versal situation of **Stacks 0DQU** let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite
type over `S`, and let `A`, `A'` be versal rings to `𝒳` at `x₀` (**Stacks 0DQV**) whose versal
formal objects `ξ`, `ξ'` come from morphisms `Spec A ⟶ 𝒳`, `Spec A' ⟶ 𝒳` (**Stacks 07X8**).
Part (1) of **Stacks 0DR1** says that the comparison `A ≅ A'[[t₁, …, t_r]]` of **Stacks 0DQX**
(or the one with `A`, `A'` exchanged) can be chosen compatibly with these morphisms; the remark
then notes that the resulting triangles only commute up to a noncanonical `2`-arrow, and closes
with: *still, this means that the implied map `A' → A` or `A → A'` in (1) is well defined up to
formal homotopy* (**Stacks 0DQD**).

This file proves that closing claim. The realizations are those of
`Deformation.Artin.FormalObject.Realization`: objects `y`, `y'` of `𝒳` over `Spec A`, `Spec A'`
with arrows from the levels of `ξ`, `ξ'`. A map `f : A' → A` is *compatible with the
realizations* when there is a `2`-arrow, i.e. a morphism `m : y ⟶ y'` of `𝒳` lying over
`Spec f : Spec A ⟶ Spec A'`, which restricts to the identity of `x₀`: composed with the arrow
`x₀ ⟶ y` through which `y` restricts to the given point, it gives the arrow `x₀ ⟶ y'`
(`Deformation.Artin.realizationPointArrow`). This is exactly what makes `m` induce an
isomorphism `f_*ξ' ≅ ξ` of formal objects of `𝓕_{𝒳,k,x₀}` (whose objects and morphisms carry
the arrows out of `x₀`, Stacks 07T2), and Stacks 0DQD then says that any two such maps are
formally homotopic. The condition at `x₀` cannot be dropped: for the quotient `[V/(ℤ/2)]` of the
node `V = Spec k[x, y]/(xy)` by the swap of the branches, with `x₀` the node, the swap `σ` of
`A = k[[x, y]]/(xy)` is compatible with `Spec A ⟶ V ⟶ 𝒳` through the nontrivial element of the
group, a `2`-arrow restricting to a nontrivial automorphism of `x₀`, and `σ` is not formally
homotopic to the identity since it exchanges the minimal primes (Stacks 0DQE).

## Main definitions

* `Deformation.Artin.realizationPointArrow`: the arrow `x₀ ⟶ y` of a realization of a formal
  object of the predeformation category.

## Main results

* `Deformation.Artin.exists_hom_of_realization_hom`: a morphism of realizing objects over
  `Spec f`, compatible with the arrows out of `x₀`, comes from a morphism of formal objects of the
  predeformation category with base map `f`.
* `AlgebraicGeometry.Stack.exists_powerSeries_comparison_realization_pointed`: the maps of
  part (1) of Stacks 0DR1 can be chosen compatible with the realizations in this sense.
* `AlgebraicGeometry.Stack.formallyHomotopic_of_realization_compatible`: **Stacks 0DR1**, the
  closing claim: any two maps `A' → A` compatible with the realizations are formally homotopic.

## Implementation notes

Formal homotopy (Stacks 0DQA) is a relation on morphisms of `\widehat{𝒞}_Λ`, for the `Λ` of the
predeformation category `𝓕_{𝒳,k,x₀}`: an affine open `Spec Λ ⊆ S` through which `Spec k ⟶ S`
factors with `Λ → k` finite (Stacks 07T2, 0DQW). So both versal rings are complete local
`Λ`-algebras over the same chart, as in the source, and the maps are morphisms of
`\widehat{𝒞}_Λ`. The statement covers both directions of part (1): for maps `A → A'` exchange the
roles of the two rings. Only the source ring of the maps needs to be versal, as in Stacks 0DQD.

## References

* [Stacks Project, Tag 0DQA](https://stacks.math.columbia.edu/tag/0DQA)
* [Stacks Project, Tag 0DQD](https://stacks.math.columbia.edu/tag/0DQD)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation

universe u w u₁ v₁

section Tangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- The tangent module at the rank-one module `ULift k` of a deformation category is
finite-dimensional as soon as its lifted tangent space `tangentSpaceArtinian` is: the converse of
`Deformation.finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt`. -/
theorem finiteDimensional_tangentModuleAt_of_tangentSpaceArtinian
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
    (hfin : letI : Fact (IsPredeformationCategory.{u, w, w} (BasedCategory.ofFunctor 𝓕.p).p) :=
        ⟨h𝓕.predeformation⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor 𝓕.p) h𝓕.predeformation.cofibered))) :=
        ⟨tangentConditionS2.{u, w, w} h𝓕⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
        (isomorphismClasses (BasedCategory.ofFunctor 𝓕.p) h𝓕.predeformation.cofibered))) :
    FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 (FGModuleCat.of k (ULift.{w} k))) := by
  let : Fact (IsPredeformationCategory.{u, w, w} 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨tangentConditionS2.{u, w, w} h𝓕⟩
  have : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) := hfin
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, w, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, w, w} h𝓕)).symm.finiteDimensional

end Tangent

end Deformation

namespace Deformation.Artin

universe u v w

/-! ### Reversed arrows of deformations lying over a given ring map -/

section ArrowBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  {iΛ : Spec (.of Λ) ⟶ S} {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The condition `arrow_base` of a morphism of deformations, for a ring map given through
identifications of the two Artinian algebras: an arrow of `X` lying over `Spec g`, read through
any identifications of the underlying schemes, lies over the spectrum of the transported map. -/
theorem deformationMorphism_arrow_base_of_eq {a b : DeformationObject iΛ q x₀ hx₀}
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (ha : a.algebra = A') (hb : b.algebra = A)
    (g : A' ⟶ A) (c : b.point ⟶ a.point)
    (hL : (q.obj a.point).left = Spec (.of A')) (hL' : (q.obj b.point).left = Spec (.of A))
    (h : eqToHom hL'.symm ≫ (q.map c).left ≫ eqToHom hL =
      Spec.map (CommRingCat.ofHom g.hom.toRingHom)) :
    eqToHom (congrArg Over.left b.base).symm ≫ (q.map c).left ≫
        eqToHom (congrArg Over.left a.base) =
      Spec.map (CommRingCat.ofHom (eqToHom ha ≫ g ≫ eqToHom hb.symm).hom.toRingHom) := by
  subst ha hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact h

end ArrowBase

/-! ### The point of a realization -/

section Pointing

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}
  {x₀ : F} {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- **The arrow `x₀ ⟶ y` of a realization.** If `y` realizes (the formal object over the site of)
a formal object `ξ` of the predeformation category `𝓕_{𝒳,k,x₀}`, the arrow `x₀ ⟶ ξ_0` of the
deformation at level zero followed by the arrow `ξ_0 ⟶ y` of the realization is the arrow through
which `y` restricts to the point `x₀`. -/
def realizationPointArrow
    {ξ : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {hA : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base.R))} {y : F}
    {hy : p.obj y = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base hA}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy) :
    x₀ ⟶ y :=
  ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects (ξ.level 0)).arrow ≫
    R.r 0

/-- The arrow `x₀ ⟶ ξ_n` of the deformation at any level, followed by the arrow `ξ_n ⟶ y` of the
realization, is the arrow `x₀ ⟶ y` of the realization. -/
theorem arrow_comp_realization_r
    {ξ : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {hA : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base.R))} {y : F}
    {hy : p.obj y = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base hA}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy)
    (n : ℕ) :
    ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects (ξ.level n)).arrow ≫
      R.r n = realizationPointArrow R := by
  let P := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := P.category
  induction n with
  | zero => rfl
  | succ n ih =>
    calc (P.objects (ξ.level (n + 1))).arrow ≫ R.r (n + 1)
        = ((P.objects (ξ.level n)).arrow ≫ (P.morphisms _ _ (ξ.transition n)).arrow) ≫
            R.r (n + 1) :=
          congrArg (· ≫ R.r (n + 1)) (P.morphisms _ _ (ξ.transition n)).triangle.symm
      _ = (P.objects (ξ.level n)).arrow ≫ ((P.morphisms _ _ (ξ.transition n)).arrow ≫
            R.r (n + 1)) := Category.assoc _ _ _
      _ = (P.objects (ξ.level n)).arrow ≫ R.r n := congrArg _ (R.comp_transition n)
      _ = realizationPointArrow R := ih

/-- The map of complete local algebras `f : A' ⟶ A` and the maps of their truncations commute with
the inclusions of the infinitesimal thickenings `Spec (A / m_A ^ (n + 1)) ⟶ Spec A`. -/
private theorem spec_map_truncation_comp_adicThickeningι {A A' : CompleteLocalAlgCat.{u, u, u} Λ k}
    (f : A' ⟶ A) (n : ℕ) :
    Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom) ≫
        adicThickeningι A' (maximalIdeal A') n =
      adicThickeningι A (maximalIdeal A) n ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  have e₁ := Spec.map_comp
    (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A' ^ (n + 1))) :
      CommRingCat.of A' ⟶ CommRingCat.of ((AdicTruncation.functor n).obj A'))
    (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom)
  have e₂ := Spec.map_comp (CommRingCat.ofHom f.hom.toRingHom)
    (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))
  rw [adicThickeningι, adicThickeningι]
  refine e₁.symm.trans (Eq.trans ?_ e₂)
  congr 1

/-- The spectrum of a map of complete local `Λ`-algebras commutes with the structure maps to `S`
through `Spec Λ`. -/
private theorem spec_map_comp_algebraMap_comp {A A' : CompleteLocalAlgCat.{u, u, u} Λ k}
    (f : A' ⟶ A) :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact f.hom.comp_algebraMap

/-- Over a category fibred in groupoids, the arrows `ζ_n ⟶ y` of a realization are
monomorphisms. -/
private theorem FormalObject.Realization.mono_r (hp : p.IsFiberedInGroupoids)
    {ζ : FormalObject B S hS p} {hA : B.Contains (Spec (.of ζ.base.R))} {y : F}
    {hy : p.obj y = baseOver B S hS ζ.base hA} (R : ζ.Realization hA y hy) (n : ℕ) :
    Mono (R.r n) := by
  constructor
  intro z c₁ c₂ h
  have : Mono (p.map (R.r n)) := by
    rw [R.map_eq]
    exact mono_comp (eqToHom (ζ.level_eq n)) _
  have hpc : p.map c₁ = p.map c₂ := by
    rw [← cancel_mono (p.map (R.r n)), ← Functor.map_comp, ← Functor.map_comp, h]
  obtain ⟨χ, -, hχ⟩ := hp.unique_lift (R.r n) (c₂ ≫ R.r n) (p.map c₁)
    (by rw [← Functor.map_comp, h])
  exact (hχ c₁ ⟨rfl, h⟩).trans (hχ c₂ ⟨hpc.symm, rfl⟩).symm

/-- A morphism `m : y ⟶ y'` of realizing objects lying over `Spec f` lifts, level by level, to
arrows `ζ_n ⟶ ζ'_n` lying over the maps of the infinitesimal thickenings induced by `f` and
compatible with `m` through the arrows of the realizations. -/
private theorem exists_lift_of_realization_hom (hp : p.IsFiberedInGroupoids)
    {ξ ξ' : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {hA : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base.R))}
    {hA' : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base.R))} {y y' : F}
    {hy : p.obj y = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base hA}
    {hy' : p.obj y' = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base hA'}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy)
    (R' : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ').Realization hA' y' hy')
    (f : ξ'.base ⟶ ξ.base) (m : y ⟶ y')
    (hm : (BigFppfOver.toScheme B S hS).map (eqToHom hy.symm ≫ p.map m ≫ eqToHom hy') =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom)) :
    ∃ ψ : ∀ n, (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).level n ⟶
        (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ').level n,
      (∀ n, ψ n ≫ R'.r n = R.r n ≫ m) ∧
      ∀ n, eqToHom (congrArg Over.left
          (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ.level_eq n))).symm ≫
        ((p ⋙ Over.post B.inclusion).map (ψ n)).left ≫ eqToHom (congrArg Over.left
          (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ'.level_eq n))) =
        Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom) := by
  let P := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := P.category
  set ζ := FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ
  set ζ' := FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ'
  let T : ∀ n, truncationOver B S hS ζ.base ζ.contains n ⟶
      truncationOver B S hS ζ'.base ζ'.contains n := fun n =>
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom))) (by
        apply ObjectProperty.hom_ext
        show Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom) ≫
            adicThickeningι ξ'.base (maximalIdeal ξ'.base) n ≫
              Spec.map (CommRingCat.ofHom (algebraMap Λ ξ'.base)) ≫ iΛ =
          adicThickeningι ξ.base (maximalIdeal ξ.base) n ≫
            Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (spec_map_truncation_comp_adicThickeningι f n)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (spec_map_comp_algebraMap_comp (iΛ := iΛ) f)))))
  have hT : ∀ n, T n ≫ restrictionToBase B S hS ζ'.base hA' ζ'.contains n =
      restrictionToBase B S hS ζ.base hA ζ.contains n ≫
        (eqToHom hy.symm ≫ p.map m ≫ eqToHom hy') := by
    intro n
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, restrictionToBase_toScheme,
      restrictionToBase_toScheme, hm]
    exact spec_map_truncation_comp_adicThickeningι f n
  let t : ∀ n, p.obj (ζ.level n) ⟶ p.obj (ζ'.level n) := fun n =>
    eqToHom (ζ.level_eq n) ≫ T n ≫ eqToHom (ζ'.level_eq n).symm
  have hθ : ∀ n, t n ≫ p.map (R'.r n) = p.map (R.r n ≫ m) := by
    intro n
    rw [R'.map_eq, Functor.map_comp, R.map_eq]
    simp only [t, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (hT n)]
    simp
    rfl
  choose ψ hψ using fun n => (hp.unique_lift (R'.r n) (R.r n ≫ m) (t n) (hθ n)).exists
  have hL : ∀ (η : Deformation.FormalObject P.projection) (n : ℕ),
      ((p ⋙ Over.post B.inclusion).obj (P.objects (η.level n)).point).left =
        Spec (.of ((AdicTruncation.functor n).obj η.base)) := fun η n =>
    congrArg Over.left (predeformation_point_over B S hS iΛ p x₀ hx₀ (η.level_eq n))
  have hLζ : ∀ n, (p.obj (ζ.level n)).left.obj =
      Spec (.of ((AdicTruncation.functor n).obj ξ.base)) := hL ξ
  have hLζ' : ∀ n, (p.obj (ζ'.level n)).left.obj =
      Spec (.of ((AdicTruncation.functor n).obj ξ'.base)) := hL ξ'
  have harrow : ∀ n, eqToHom (hLζ n).symm ≫ (p.map (ψ n)).left.hom ≫ eqToHom (hLζ' n) =
      Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom) := by
    intro n
    simp only [(hψ n).1, t]
    rw [bigFppfOver_left_hom_eqToHom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl
  exact ⟨ψ, fun n => (hψ n).2, harrow⟩

/-- Arrows `ζ_n ⟶ ζ'_n` between the levels of realized formal objects, compatible with the arrows
out of `x₀`, lying over the maps of the thickenings induced by `f` and compatible with a morphism
`m` of the realizing objects, form a morphism of formal objects `ξ' ⟶ ξ` with base map `f`. -/
private theorem exists_hom_of_lifts (hp : p.IsFiberedInGroupoids)
    {ξ ξ' : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {hA : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base.R))}
    {hA' : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base.R))} {y y' : F}
    {hy : p.obj y = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base hA}
    {hy' : p.obj y' = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base hA'}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy)
    (R' : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ').Realization hA' y' hy')
    (f : ξ'.base ⟶ ξ.base) (m : y ⟶ y')
    (ψ : ∀ n, (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).level n ⟶
      (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ').level n)
    (hψ : ∀ n, ψ n ≫ R'.r n = R.r n ≫ m)
    (htri : ∀ n, ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
      (ξ.level n)).arrow ≫ ψ n =
        ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
          (ξ'.level n)).arrow)
    (harrow : ∀ n, eqToHom (congrArg Over.left
        (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ.level_eq n))).symm ≫
      ((p ⋙ Over.post B.inclusion).map (ψ n)).left ≫ eqToHom (congrArg Over.left
        (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ'.level_eq n))) =
      Spec.map (CommRingCat.ofHom ((AdicTruncation.functor n).map f).hom.toRingHom)) :
    ∃ a : ξ' ⟶ ξ, a.base = f := by
  let P := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := P.category
  let app : ∀ n, ξ'.level n ⟶ ξ.level n := fun n =>
    (P.morphisms (ξ'.level n) (ξ.level n)).symm
      { ringHom := eqToHom (ξ'.level_eq n) ≫ (AdicTruncation.functor n).map f ≫
          eqToHom (ξ.level_eq n).symm
        arrow := ψ n
        triangle := htri n
        arrow_base := deformationMorphism_arrow_base_of_eq (ξ'.level_eq n) (ξ.level_eq n)
          ((AdicTruncation.functor n).map f) (ψ n)
          (congrArg Over.left (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ'.level_eq n)))
          (congrArg Over.left (predeformation_point_over B S hS iΛ p x₀ hx₀ (ξ.level_eq n)))
          (harrow n) }
  have happ_lift : ∀ n, P.projection.IsHomLift ((AdicTruncation.functor n).map f) (app n) := by
    intro n
    apply IsHomLift.of_fac _ _ _ (ξ'.level_eq n) (ξ.level_eq n)
    show _ = eqToHom _ ≫ (eqToHom _ ≫ (AdicTruncation.functor n).map f ≫ eqToHom _) ≫
      eqToHom _
    simp
  refine ⟨{ base := f, app := app, app_lift := happ_lift, naturality := fun n => ?_ }, rfl⟩
  apply (P.morphisms _ _).injective
  apply DeformationMorphism.ext_of_components
  · rw [← P.morphism_projection, ← P.morphism_projection]
    congr 2
    have h₁ : P.projection.IsHomLift
        ((AdicTruncation.transitionNat n).app ξ'.base ≫ (AdicTruncation.functor n).map f)
        (ξ'.transition n ≫ app n) :=
      have := ξ'.transition_lift n; have := happ_lift n; inferInstance
    have h₂ : P.projection.IsHomLift
        ((AdicTruncation.functor (n + 1)).map f ≫ (AdicTruncation.transitionNat n).app ξ.base)
        (app (n + 1) ≫ ξ.transition n) :=
      have := ξ.transition_lift n; have := happ_lift (n + 1); inferInstance
    rw [(AdicTruncation.transitionNat n).naturality f] at h₂
    rw [IsHomLift.fac' P.projection
        ((AdicTruncation.transitionNat n).app ξ'.base ≫ (AdicTruncation.functor n).map f)
        (ξ'.transition n ≫ app n),
      IsHomLift.fac' P.projection
        ((AdicTruncation.transitionNat n).app ξ'.base ≫ (AdicTruncation.functor n).map f)
        (app (n + 1) ≫ ξ.transition n)]
  · rw [P.reversed_composition, P.reversed_composition]
    show ψ n ≫ (P.morphisms _ _ (ξ'.transition n)).arrow =
      (P.morphisms _ _ (ξ.transition n)).arrow ≫ ψ (n + 1)
    exact (R'.mono_r hp (n + 1)).right_cancellation _ _ ((Category.assoc _ _ _).trans
      ((congrArg (fun g => ψ n ≫ g) (R'.comp_transition n)).trans ((hψ n).trans
        ((congrArg (fun g => g ≫ m) (R.comp_transition n).symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun g => (P.morphisms _ _ (ξ.transition n)).arrow ≫ g)
            (hψ (n + 1)).symm).trans (Category.assoc _ _ _).symm))))))

/-- **A morphism of realizing objects compatible with the points comes from a morphism of formal
objects of the predeformation category.** Let `y`, `y'` realize formal objects `ξ`, `ξ'` of
`𝓕_{𝒳,k,x₀}` and let `f : A' ⟶ A` be a map of their complete local bases. A morphism `m : y ⟶ y'`
lying over `Spec f` and compatible with the arrows out of `x₀` restricts to a morphism of formal
objects `ξ' ⟶ ξ` of the predeformation category with base map `f`: an isomorphism `f_*ξ' ≅ ξ`. -/
theorem exists_hom_of_realization_hom (hp : p.IsFiberedInGroupoids)
    {ξ ξ' : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {hA : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base.R))}
    {hA' : B.Contains (Spec (.of (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base.R))} {y y' : F}
    {hy : p.obj y = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ).base hA}
    {hy' : p.obj y' = baseOver B S hS (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite
      ξ').base hA'}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy)
    (R' : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ').Realization hA' y' hy')
    (f : ξ'.base ⟶ ξ.base) (m : y ⟶ y')
    (hm : (BigFppfOver.toScheme B S hS).map (eqToHom hy.symm ≫ p.map m ≫ eqToHom hy') =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    (hpt : realizationPointArrow R ≫ m = realizationPointArrow R') :
    ∃ a : ξ' ⟶ ξ, a.base = f := by
  let P := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := P.category
  obtain ⟨ψ, hψ, harrow⟩ := exists_lift_of_realization_hom hp R R' f m hm
  refine exists_hom_of_lifts hp R R' f m ψ hψ (fun n => ?_) harrow
  apply (R'.mono_r hp n).right_cancellation
  erw [Category.assoc, hψ n, ← Category.assoc, arrow_comp_realization_r R n, hpt,
    arrow_comp_realization_r R' n]

end Pointing

end Deformation.Artin

namespace AlgebraicGeometry.Stack

universe u w

variable (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})

/-- **The maps of Stacks 0DR1, part (1), compatible with the points.** Over one chart `Spec Λ` of
`S` with `Λ → k` finite, let `A`, `A'` be versal rings to `𝒳` at `x₀` whose versal formal objects
`ξ`, `ξ'` are realized by objects `y`, `y'` of `𝒳` over `Spec A`, `Spec A'`. Then either there are
an isomorphism `E : A ≅ A'[[t₁, …, t_r]]` of `Λ`-algebras and a map `φ : A' ⟶ A` of
`\widehat{𝒞}_Λ` with `E ∘ φ` the inclusion of constants, together with a morphism `y ⟶ y'` of `𝒳`
lying over `Spec φ` and compatible with the arrows out of `x₀`; or the same with `A` and `A'`
exchanged. These are the maps that
`AlgebraicGeometry.Stack.formallyHomotopic_of_realization_compatible` shows to be well defined up
to formal homotopy. -/
theorem exists_powerSeries_comparison_realization_pointed
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ').Realization hA' y' hy') :
    (∃ r : ℕ, ∃ E : ξ.base ≃ₐ[Λ] MvPowerSeries (Fin r) ξ'.base, ∃ φ : ξ'.base ⟶ ξ.base,
      (∀ b, E (φ.hom b) = MvPowerSeries.C b) ∧
      ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
          Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Ry ≫ m =
          Deformation.Artin.realizationPointArrow Ry') ∨
    (∃ r : ℕ, ∃ E : ξ'.base ≃ₐ[Λ] MvPowerSeries (Fin r) ξ.base, ∃ φ : ξ.base ⟶ ξ'.base,
      (∀ b, E (φ.hom b) = MvPowerSeries.C b) ∧
      ∃ m : y' ⟶ y, (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
          Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Ry' ≫ m =
          Deformation.Artin.realizationPointArrow Ry) := by
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion iΛ)
  let P := Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
  let := P.category
  have hfull := Deformation.Artin.full_approximationFunctor_algebraicStacks D.𝒳
  -- a morphism of formal objects gives a morphism of the realizing objects, compatible with
  -- the points
  have key : ∀ {η η' : Deformation.FormalObject P.projection}
      {hB : D.B.Contains (Spec (.of η.base))} {hB' : D.B.Contains (Spec (.of η'.base))}
      {z z' : D.𝒳.val.val.obj}
      {hz : D.𝒳.val.val.p.obj z = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite η.base) hB}
      {hz' : D.𝒳.val.val.p.obj z' = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite η'.base) hB'}
      (Rz : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀
        hx₀ hfinite η).Realization hB z hz)
      (Rz' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀
        hx₀ hfinite η').Realization hB' z' hz') (φ : η' ⟶ η),
      ∃ m : z ⟶ z', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hz.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hz') =
          Spec.map (CommRingCat.ofHom φ.base.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Rz ≫ m =
          Deformation.Artin.realizationPointArrow Rz' := by
    intro η η' hB hB' z z' hz hz' Rz Rz' φ
    obtain ⟨m, hmr, hm⟩ := Deformation.Artin.FormalObject.Realization.exists_hom
      D.𝒳.val.property hfull Rz Rz'
      (Deformation.Artin.FormalObject.ofPredeformationMap D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite φ)
    refine ⟨m, hm _ (Deformation.Artin.FormalObject.ofPredeformationMap_isBaseMap D.B D.S D.hS
      iΛ D.𝒳.val.val.p x₀ hx₀ hfinite φ), ?_⟩
    change (_ ≫ Rz.r 0) ≫ m = _ ≫ Rz'.r 0
    erw [Category.assoc, hmr 0, ← Category.assoc, (P.morphisms _ _ (φ.app 0)).triangle]
  rcases Deformation.exists_powerSeries_comparison_hom
      (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property) ξ ξ' hξ hξ' with
    ⟨r, E, φ, hE⟩ | ⟨r, E, φ, hE⟩
  · exact Or.inl ⟨r, E, φ.base, hE, key Ry Ry' φ⟩
  · exact Or.inr ⟨r, E, φ.base, hE, key Ry' Ry φ⟩

/-- **Stacks 0DR1, closing claim: the map of part (1) is well defined up to formal homotopy.** In
the versal situation of Stacks 0DQU, let `x₀` be a point of `𝒳` over `Spec k` for a field `k` of
finite type over `S`, presented over an affine open `Spec Λ ⊆ S` with `Λ → k` finite, so that
`𝓕_{𝒳,k,x₀}` lives over `𝒞_Λ` (Stacks 07T2). Let `A'` be a versal ring to `𝒳` at `x₀` with versal
formal object `ξ'`, let `A` be the base of a formal object `ξ` of `𝓕_{𝒳,k,x₀}` (for instance a
second versal ring), and let `y'`, `y` be objects of `𝒳` over `Spec A'`, `Spec A` realizing `ξ'`,
`ξ`, i.e. morphisms `Spec A' ⟶ 𝒳`, `Spec A ⟶ 𝒳` from which the formal objects come (Stacks 07X8).
Then any two maps `f, g : A' ⟶ A` of `\widehat{𝒞}_Λ` compatible with these morphisms — each
admitting a `2`-arrow `y ⟶ y'` lying over its spectrum and restricting to the identity of `x₀` —
are formally homotopic (Stacks 0DQA). Applied with `A`, `A'` in either order this covers both the
maps `A' → A` and `A → A'` of part (1) (see
`AlgebraicGeometry.Stack.exists_powerSeries_comparison_realization_pointed`), and it is
Stacks 0DQD, which applies since `𝓕_{𝒳,k,x₀}` is a deformation category with finite-dimensional
tangent space and infinitesimal automorphisms (Stacks 0DQW). -/
@[stacks 0DR1 "closing claim: the map in (1) is well defined up to formal homotopy (0DQD)"]
theorem formallyHomotopic_of_realization_compatible
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ').Realization hA' y' hy')
    (f g : ξ'.base ⟶ ξ.base)
    (hf : ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
        (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Ry ≫ m =
          Deformation.Artin.realizationPointArrow Ry')
    (hg : ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
        (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
          Spec.map (CommRingCat.ofHom g.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Ry ≫ m =
          Deformation.Artin.realizationPointArrow Ry') :
    Deformation.CompleteLocalAlgCat.FormallyHomotopic f g := by
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion iΛ)
  let P := Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
  let := P.category
  have H : ∀ h : ξ'.base ⟶ ξ.base, (∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
        (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
          Spec.map (CommRingCat.ofHom h.hom.toRingHom) ∧
        Deformation.Artin.realizationPointArrow Ry ≫ m =
          Deformation.Artin.realizationPointArrow Ry') → ∃ a : ξ' ⟶ ξ, a.base = h :=
    fun h ⟨m, hm, hpt⟩ =>
      Deformation.Artin.exists_hom_of_realization_hom D.𝒳.val.property Ry Ry' h m hm hpt
  obtain ⟨af, haf⟩ := H f hf
  obtain ⟨ag, hag⟩ := H g hg
  obtain ⟨hp, hT, hInf⟩ :=
    isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ hiΛ x₀ hx₀ hfinite
  exact Deformation.formallyHomotopic_of_isVersal P.projection hp
    (Deformation.finiteDimensional_tangentModuleAt_of_tangentSpaceArtinian hp hT)
    (fun x PF hx => hInf x hx PF) ξ' ξ hξ' f g ⟨af, haf⟩ ⟨ag, hag⟩

end AlgebraicGeometry.Stack

end
