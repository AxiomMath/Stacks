module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeCartesianLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectArrowFactorization
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianCompositionCancellation
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite

/-!
# Modules in the faithful `LQCoh^fbc` are cartesian between flat objects over affines

Let `𝒳` be an algebraic stack and `𝓕` a module in the faithful `LQCoh^fbc(𝒪_𝒳)` (Stacks 06WJ and
0762 with the pullback of sheaves) with sections in `Type (u + 1)`. For every arrow `φ : z ⟶ y`
between *flat* objects of `𝒳` lying over affine schemes — `φ` itself need not lie over a flat
morphism — the base-change comparison `𝒪(z) ⊗_{𝒪(y)} 𝓕(y) ⟶ 𝓕(z)` is bijective.

Étale locally on its source, `φ` factors through arrows lying over flat morphisms
(`AlgebraicGeometry.Stack.FlatFppf.exists_flat_factorization`); `𝓕` is cartesian along arrows over
flat and over étale morphisms of affine schemes, cartesianness passes to composites and cancels,
and it descends along a finite étale covering of the affine source, whose rings of functions are
jointly faithfully flat. This is the sections-level form of the step of Stacks 07B1 (2)(b) that the
comparison map is an isomorphism along every arrow between flat objects.

## Main results

* `AlgebraicGeometry.Stack.exists_isAffine_bijective_restrictionBaseChange_of_factorization`.
* `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_etale_cover`.
* `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_flatObject`.

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The arrow `ι_T : x_T ⟶ x` from the image of an object `T` of the small étale site of the
scheme below `x` under the index functor of Stacks 06W1 to `x`. -/
noncomputable abbrev etaleIndexArrow (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    (etaleIndex B E h S hS p hp x).obj T ⟶ x :=
  letI := isEquivalence_overPost B S hS p hp x
  ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj T)).hom

/-- The scheme morphism below `ι_T` is the structure morphism of `T`, up to the identification of
Stacks 06W0 of the scheme below `x_T` with the scheme of `T`. -/
theorem inclusion_map_etaleIndexArrow (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    B.inclusion.map (p.map (etaleIndexArrow B E h S hS p hp x T)).left =
      (etaleIndexIso B E h S hS p hp x T).hom ≫ E.inclusion.map T.obj.hom := by
  let := isEquivalence_overPost B S hS p hp x
  have := Over.w ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.hom.app
    ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj T))
  have h2 := congrArg (fun k => B.inclusion.map k) this
  simp only [Functor.map_comp] at h2
  exact h2.symm

/-- The arrow `ι_T` is compatible with the index functor. -/
@[reassoc]
theorem etaleIndex_map_etaleIndexArrow (x : 𝒳)
    {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (g : T ⟶ T') :
    (etaleIndex B E h S hS p hp x).map g ≫ etaleIndexArrow B E h S hS p hp x T' =
      etaleIndexArrow B E h S hS p hp x T := by
  let := isEquivalence_overPost B S hS p hp x
  exact Over.w ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.map
    ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).map g))

/-- The arrow `ι_T` lies over an étale morphism of schemes. -/
theorem etale_etaleIndexArrow (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    Etale (B.inclusion.map (p.map (etaleIndexArrow B E h S hS p hp x T)).left) := by
  rw [inclusion_map_etaleIndexArrow]
  infer_instance

variable (F : PresheafOfModules.{max (u + 1) v w m}
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
  (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, max (u + 1) v w m}
    B E h S hS p hp F)

/-- The scheme morphism below a composite of arrows is the composite of the scheme morphisms. -/
private theorem inclusion_map_comp_left {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) :
    B.inclusion.map (p.map (f ≫ g)).left =
      B.inclusion.map (p.map f).left ≫ B.inclusion.map (p.map g).left := by
  rw [Functor.map_comp, Over.comp_left, Functor.map_comp]

include hF

/-- Along an arrow lying over a flat morphism of affine schemes a module in the faithful
`LQCoh^fbc` is cartesian. -/
theorem bijective_restrictionBaseChange_of_flat_freeModuleUniverse {a b : 𝒳} (ψ : a ⟶ b)
    (hψ : Flat (B.inclusion.map (p.map ψ).left))
    (ha : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj a))
    (hb : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj b)) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F ψ.op) :=
  bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison.{u, v, w, m}
    B E h S hS p hp F hF.1 ψ (hF.2 ψ hψ) ha hb

/-- **Cartesianness along a chart of the first factor of a flat factorization**: if the composite
`κ ≫ φ` of an étale arrow `κ : z' ⟶ z` factors as `χ ≫ π₂` with `χ ≫ π₁ = κ` and `π₁`, `π₂` lying
over flat morphisms, the module is cartesian along `ι_V ≫ κ ≫ φ` for every affine chart `V` of `z'`
mapping to the base change along `χ` of an affine chart `U` of the source of `π₁`. -/
private theorem bijective_restrictionBaseChange_etaleIndexArrow_comp_of_factorization
    {z z' x y : 𝒳} (φ : z ⟶ y) (κ : z' ⟶ z) (χ : z' ⟶ x) (π₁ : x ⟶ z) (π₂ : x ⟶ y)
    (hκ : Etale (B.inclusion.map (p.map κ).left))
    (hπ₁ : Flat (B.inclusion.map (p.map π₁).left)) (hπ₂ : Flat (B.inclusion.map (p.map π₂).left))
    (h₁ : χ ≫ π₁ = κ) (h₂ : χ ≫ π₂ = κ ≫ φ)
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (U : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x))
    (hU : IsAffine ((SmallEtale.toScheme E _ _).obj U))
    (V : SmallEtale E (p.obj z').left.1 (contains_base B E h S hS p z'))
    (hV : IsAffine ((SmallEtale.toScheme E _ _).obj V))
    (kV : V ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p χ)).obj U) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F (etaleIndexArrow B E h S hS p hp z' V ≫ κ ≫ φ).op) := by
  let := isEquivalence_overPost B S hS p hp x
  let := isEquivalence_overPost B S hS p hp z'
  obtain ⟨φ', hfac, -⟩ := exists_restrictionComparisonLift B E h S hS p hp χ U
  let ιU := etaleIndexArrow B E h S hS p hp x U
  let ιV := etaleIndexArrow B E h S hS p hp z' V
  let m := (etaleIndex B E h S hS p hp z').map kV
  have hfac' : φ' ≫ ιU = etaleIndexArrow B E h S hS p hp z'
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p χ)).obj U) ≫ χ := hfac
  have ha : ιV = m ≫ etaleIndexArrow B E h S hS p hp z'
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p χ)).obj U) :=
    (etaleIndex_map_etaleIndexArrow B E h S hS p hp z' kV).symm
  have e₁ : ιV ≫ κ ≫ φ = (m ≫ φ') ≫ (ιU ≫ π₂) := by
    rw [ha, ← h₂]
    simp only [Category.assoc]
    rw [reassoc_of% hfac']
  have e₂ : (m ≫ φ') ≫ (ιU ≫ π₁) = ιV ≫ κ := by
    rw [ha, ← h₁]
    simp only [Category.assoc]
    rw [reassoc_of% hfac']
  have hVa : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj
      ((etaleIndex B E h S hS p hp z').obj V)) := isAffine_etaleIndex_obj B E h S hS p hp z' V hV
  have hUa : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj
      ((etaleIndex B E h S hS p hp x).obj U)) := isAffine_etaleIndex_obj B E h S hS p hp x U hU
  have hιU := etale_etaleIndexArrow B E h S hS p hp x U
  have hιV := etale_etaleIndexArrow B E h S hS p hp z' V
  have hfl₂ : Flat (B.inclusion.map (p.map (ιU ≫ π₂)).left) := by
    rw [inclusion_map_comp_left]
    infer_instance
  have hfl₁ : Flat (B.inclusion.map (p.map (ιU ≫ π₁)).left) := by
    rw [inclusion_map_comp_left]
    infer_instance
  have het : Etale (B.inclusion.map (p.map (ιV ≫ κ)).left) := by
    rw [inclusion_map_comp_left]
    infer_instance
  have hβ₂ := bijective_restrictionBaseChange_of_flat_freeModuleUniverse.{u, v, w, m}
    B E h S hS p hp F hF (ιU ≫ π₂) hfl₂ hUa hy
  have hβm : Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F (m ≫ φ').op) := by
    refine bijective_restrictionBaseChange_of_comp.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F (ιU ≫ π₁).op (m ≫ φ').op
      (bijective_restrictionBaseChange_of_flat_freeModuleUniverse.{u, v, w, m}
        B E h S hS p hp F hF (ιU ≫ π₁) hfl₁ hUa hz) ?_
    rw [← op_comp, e₂]
    exact bijective_restrictionBaseChange_of_isLocallyQuasicoherent_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp F hF.1 (ιV ≫ κ) het hVa hz
  rw [e₁, op_comp, ← ConcreteCategory.isIso_iff_bijective]
  rw [← ConcreteCategory.isIso_iff_bijective] at hβ₂ hβm
  exact isIso_restrictionBaseChange_comp.{v, w, u, max (u + 1) v w m}
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    F _ _ hβ₂ hβm

/-- **Cartesianness along the composite of the first factor of a flat factorization**: étale
locally on the source of an étale arrow `κ : z' ⟶ z`, along which the composite `κ ≫ φ` factors
as `χ ≫ π₂` with `χ ≫ π₁ = κ` and `π₁`, `π₂` lying over flat morphisms, the module is cartesian
along `ι ≫ κ ≫ φ` for the arrows `ι` from small étale charts over affine schemes. -/
theorem exists_isAffine_bijective_restrictionBaseChange_of_factorization
    {z z' x y : 𝒳} (φ : z ⟶ y) (κ : z' ⟶ z) (χ : z' ⟶ x) (π₁ : x ⟶ z) (π₂ : x ⟶ y)
    (hκ : Etale (B.inclusion.map (p.map κ).left))
    (hπ₁ : Flat (B.inclusion.map (p.map π₁).left)) (hπ₂ : Flat (B.inclusion.map (p.map π₂).left))
    (h₁ : χ ≫ π₁ = κ) (h₂ : χ ≫ π₂ = κ ≫ φ)
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (s : B.inclusion.obj (p.obj z').left) :
    ∃ V : SmallEtale E (p.obj z').left.1 (contains_base B E h S hS p z'),
      IsAffine ((SmallEtale.toScheme E _ _).obj V) ∧
        s ∈ Set.range (E.inclusion.map V.obj.hom) ∧
        Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
          (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
          F (etaleIndexArrow B E h S hS p hp z' V ≫ κ ≫ φ).op) := by
  let topX := SmallEtale.final E (p.obj x).left.1 (contains_base B E h S hS p x)
  let topZ := SmallEtale.final E (p.obj z').left.1 (contains_base B E h S hS p z')
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p χ)
  have hbT : IsTerminal (b.obj topX) := (SmallEtale.finalIsTerminal E _ _).isTerminalObj b
  let eT := hbT.uniqueUpToIso (SmallEtale.finalIsTerminal E _ (contains_base B E h S hS p z'))
  have hcov := SmallEtale.generate_isAffine_mem_topology E _ (contains_base B E h S hS p x) topX
  have hcov' := (CoverPreserving.of_isContinuous (F := b)
    (J := SmallEtale.topology E _ (contains_base B E h S hS p x))
    (K := SmallEtale.topology E _ (contains_base B E h S hS p z'))).cover_preserve hcov
  let s' : (SmallEtale.toScheme E _ _).obj topZ := s
  obtain ⟨V₁, g₁, hg₁, r₁, hr₁⟩ := SmallEtale.exists_mem_arrows_mem_range E _ _ hcov'
    ((SmallEtale.toScheme E _ _).map eT.inv s')
  obtain ⟨Z, gZ, hZ, ⟨U, k₁, k₂, hU, rfl⟩, rfl⟩ := hg₁
  obtain ⟨V₂, g₂, ⟨V, c₁, c₂, hV, rfl⟩, r₂, hr₂⟩ := SmallEtale.exists_mem_arrows_mem_range E _ _
    (SmallEtale.generate_isAffine_mem_topology E _ _ V₁) r₁
  refine ⟨V, hV, ⟨(SmallEtale.toScheme E _ _).map c₁ r₂, ?_⟩,
    bijective_restrictionBaseChange_etaleIndexArrow_comp_of_factorization.{u, v, w, m}
      B E h S hS p hp F hF φ κ χ π₁ π₂ hκ hπ₁ hπ₂ h₁ h₂ hz hy U hU V hV (c₂ ≫ hZ ≫ b.map k₁)⟩
  have hw := Over.w (c₂ ≫ (hZ ≫ b.map (k₁ ≫ k₂)) ≫ eT.hom).hom
  change _ ≫ 𝟙 _ = _ at hw
  rw [Category.comp_id] at hw
  have e1 : (SmallEtale.toScheme E _ _).map c₂ ((SmallEtale.toScheme E _ _).map c₁ r₂) = r₁ := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    exact hr₂
  have e2 : (SmallEtale.toScheme E _ _).map (c₂ ≫ (hZ ≫ b.map (k₁ ≫ k₂)) ≫ eT.hom)
      ((SmallEtale.toScheme E _ _).map c₁ r₂) =
      (SmallEtale.toScheme E _ _).map eT.hom ((SmallEtale.toScheme E _ _).map eT.inv s') := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, e1, Functor.map_comp, Scheme.Hom.comp_apply,
      hr₁]
  have e3 : (SmallEtale.toScheme E _ _).map eT.hom ((SmallEtale.toScheme E _ _).map eT.inv s') =
      s' := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [← hw]
  exact e2.trans e3

omit hF in
/-- The point bookkeeping of a chart: a point in the image of the structure morphism of `T` is in
the image of the scheme morphism below `ι_T ≫ f`, for any arrow `f`. -/
theorem mem_range_etaleIndexArrow_comp {x x' : 𝒳}
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) (f : x ⟶ x')
    (s : B.inclusion.obj (p.obj x).left) (hs : s ∈ Set.range (E.inclusion.map T.obj.hom)) :
    B.inclusion.map (p.map f).left s ∈
      Set.range (B.inclusion.map (p.map (etaleIndexArrow B E h S hS p hp x T ≫ f)).left) := by
  obtain ⟨r, rfl⟩ := hs
  refine ⟨(etaleIndexIso B E h S hS p hp x T).inv r, ?_⟩
  rw [Functor.map_comp, Over.comp_left, Functor.map_comp, inclusion_map_etaleIndexArrow]
  simp only [Scheme.Hom.comp_apply]
  rw [← Scheme.Hom.comp_apply (etaleIndexIso B E h S hS p hp x T).inv, Iso.inv_hom_id]
  rfl

/-- **Cartesianness descends along a finite étale covering of an affine source**: if
`v_k ⟶ z` are finitely many arrows lying over étale morphisms of affine schemes whose images cover
the scheme below `z`, and the module is cartesian along each `v_k ⟶ z ⟶ y`, it is cartesian along
`z ⟶ y`. -/
theorem bijective_restrictionBaseChange_of_etale_cover {z y : 𝒳} (φ : z ⟶ y)
    (hza : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    {ι : Type*} [Finite ι] (v : ι → 𝒳) (a : ∀ k, v k ⟶ z)
    (ha : ∀ k, Etale (B.inclusion.map (p.map (a k)).left))
    (hva : ∀ k, IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (v k)))
    (hcov : ∀ t : B.inclusion.obj (p.obj z).left,
      ∃ k, t ∈ Set.range (B.inclusion.map (p.map (a k)).left))
    (hβ : ∀ k, Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F (a k ≫ φ).op)) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F φ.op) := by
  have hva' : ∀ k, IsAffine (B.inclusion.obj (p.obj (v k)).left) := hva
  have hza' : IsAffine (B.inclusion.obj (p.obj z).left) := hza
  have hfl : ∀ k, Flat (B.inclusion.map (p.map (a k)).left) := fun k => by
    have := ha k
    infer_instance
  have hff := Scheme.faithfullyFlat_pi_appTop (fun k => B.inclusion.obj (p.obj (v k)).left)
    (fun k => B.inclusion.map (p.map (a k)).left) (fun t => by
      obtain ⟨k, r, hr⟩ := hcov t
      exact ⟨k, r, hr⟩)
  have key := isIso_restrictionBaseChange_of_faithfullyFlat.{v, w, u, max (u + 1) v w m}
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) F
    φ.op (fun k => op (v k)) (fun k => (a k).op) hff
    (fun k => (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_restrictionBaseChange_of_isLocallyQuasicoherent_freeModuleUniverse.{u, v, w, m}
        B E h S hS p hp F hF.1 (a k) (ha k) (hva k) hza))
    (fun k => by
      rw [ConcreteCategory.isIso_iff_bijective, ← op_comp]
      exact hβ k)
  exact (ConcreteCategory.isIso_iff_bijective _).1 key

/-- **Cartesianness is étale local on an affine source**: if every point of the scheme below `z`
is in the image of an arrow `a : x ⟶ z` lying over an étale morphism of affine schemes along whose
composite `a ≫ φ` the module is cartesian, it is cartesian along `φ : z ⟶ y`. -/
private theorem bijective_restrictionBaseChange_of_etale_locally {z y : 𝒳} (φ : z ⟶ y)
    (hza : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hloc : ∀ t : B.inclusion.obj (p.obj z).left, ∃ (x : 𝒳) (a : x ⟶ z),
      Etale (B.inclusion.map (p.map a).left) ∧
        IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x) ∧
        t ∈ Set.range (B.inclusion.map (p.map a).left) ∧
        Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
          (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
          F (a ≫ φ).op)) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F φ.op) := by
  choose v a ha hva hcov hβ using hloc
  have hopen : ∀ t, IsOpen (Set.range (B.inclusion.map (p.map (a t)).left)) := fun t =>
    have := ha t
    (B.inclusion.map (p.map (a t)).left).isOpenMap.isOpen_range
  have : CompactSpace (B.inclusion.obj (p.obj z).left) := by
    have : IsAffine (B.inclusion.obj (p.obj z).left) := hza
    infer_instance
  obtain ⟨ts, hts⟩ := isCompact_univ.elim_finite_subcover
    (fun t => Set.range (B.inclusion.map (p.map (a t)).left)) hopen
    fun t _ => Set.mem_iUnion.2 ⟨t, hcov t⟩
  refine bijective_restrictionBaseChange_of_etale_cover.{u, v, w, m} B E h S hS p hp F hF φ hza
    (ι := ts) (fun k => v k) (fun k => a k) (fun k => ha k) (fun k => hva k) (fun t => ?_)
    fun k => hβ k
  obtain ⟨k, hk, r, hr⟩ := Set.mem_iUnion₂.1 (hts (Set.mem_univ t))
  exact ⟨⟨k, hk⟩, r, hr⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **A module in the faithful `LQCoh^fbc(𝒪_𝒳)` is cartesian along every arrow between flat
objects of an algebraic stack lying over affine schemes**, at module universe `u + 1`.

The arrow factors étale locally on its source through arrows lying over flat morphisms
(`AlgebraicGeometry.Stack.FlatFppf.exists_flat_factorization`); along those, and along arrows lying
over étale morphisms, the module is cartesian, and cartesianness descends along a finite étale
covering of the affine source, whose rings of functions are faithfully flat. -/
theorem bijective_restrictionBaseChange_of_flatObject
    (F : PresheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    {z y : 𝒳.val.val.obj} (hz : flatObject B S hS 𝒳.val z) (hy : flatObject B S hS 𝒳.val y)
    (φ : z ⟶ y) (hza : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hya : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y)) :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) F φ.op) := by
  set p := 𝒳.val.val.p
  have hfib := 𝒳.val.isFiberedInGroupoids
  obtain ⟨I, W, e, he, hjs, hfac⟩ := FlatFppf.exists_flat_factorization B S hS 𝒳 hz hy φ
  choose z' x κ χ π₁ π₂ hκ hπ₁ hπ₂ h₁ h₂ using hfac
  let k : ∀ i, (Over.mk (e i ≫ (p.obj z).hom) : BigFppfOver B S hS) ⟶ p.obj z :=
    fun i => Over.homMk (e i)
  have hk : ∀ i, p.IsHomLift (k i) (κ i) := hκ
  have hκe : ∀ i, B.inclusion.map (p.map (κ i)).left =
      B.inclusion.map (eqToHom (IsHomLift.domain_eq p (k i) (κ i))).left ≫
        B.inclusion.map (e i) := fun i => by
    have := hk i
    rw [IsHomLift.fac' p (k i) (κ i)]
    simp [k]
  have hetale : ∀ i, Etale (B.inclusion.map (p.map (κ i)).left) := fun i => by
    rw [hκe i]
    have := he i
    simp only [Over.eqToHom_left, eqToHom_map]
    infer_instance
  have hcov : ∀ t : B.inclusion.obj (p.obj z).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (κ i)).left) := fun t => by
    obtain ⟨i, s, hs⟩ := hjs t
    have hiso : IsIso (B.inclusion.map (eqToHom (IsHomLift.domain_eq p (k i) (κ i))).left) := by
      simp only [Over.eqToHom_left, eqToHom_map]
      infer_instance
    obtain ⟨s', hs'⟩ := (B.inclusion.map
      (eqToHom (IsHomLift.domain_eq p (k i) (κ i))).left).surjective s
    refine ⟨i, s', ?_⟩
    rw [hκe i, Scheme.Hom.comp_apply, hs', hs]
  refine bijective_restrictionBaseChange_of_etale_locally.{u, u + 1, u, u} B E h S hS p hfib F hF φ
    hza fun t => ?_
  obtain ⟨i, s, rfl⟩ := hcov t
  obtain ⟨V, hV, hsV, hβ⟩ :=
    exists_isAffine_bijective_restrictionBaseChange_of_factorization.{u, u + 1, u, u}
      B E h S hS p hfib F hF φ (κ i) (χ i) (π₁ i) (π₂ i) (hetale i) (hπ₁ i) (hπ₂ i) (h₁ i)
      (h₂ i) hza hya s
  refine ⟨_, etaleIndexArrow B E h S hS p hfib (z' i) V ≫ κ i, ?_,
    isAffine_etaleIndex_obj B E h S hS p hfib (z' i) V hV,
    mem_range_etaleIndexArrow_comp B E h S hS p hfib V (κ i) s hsV,
    by rwa [Category.assoc]⟩
  have := etale_etaleIndexArrow B E h S hS p hfib (z' i) V
  have := hetale i
  rw [inclusion_map_comp_left]
  infer_instance

end AlgebraicGeometry.Stack

end
